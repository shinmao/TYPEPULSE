use std::rc::Rc;
use std::cell::RefCell;

use rustc_hir::{
    def_id::{DefId, LocalDefId},
    BodyId, ConstContext, HirId,
};
use rustc_middle::mir::{self, TerminatorKind, StatementKind, Rvalue, Operand, CastKind};
use rustc_middle::ty::{Ty, TyCtxt, TyKind, Instance};
use rustc_span::Span;
use crate::progress_info;

use dashmap::DashMap;
use snafu::Snafu;

use crate::ir;
use crate::prelude::*;
use crate::report::ReportLevel;
use crate::visitor::{create_adt_impl_map, AdtImplMap, RelatedFnCollector, RelatedItemMap};
use crate::call_graph::CallGraph;
use crate::utils::{
    find_import_alias, 
    has_self_parameter, 
    get_method_self_ty, 
    is_trait_method,
    resolve_impl_def_id, 
    resolve_trait_impl_def_id,
};

#[derive(Debug, Snafu, Clone)]
pub enum MirInstantiationError {
    NotAvailable { def_id: DefId },
}

impl AnalysisError for MirInstantiationError {
    fn kind(&self) -> AnalysisErrorKind {
        use MirInstantiationError::*;
        match self {
            NotAvailable { .. } => AnalysisErrorKind::OutOfScope,
        }
    }
}

pub type TypePulseCtxt<'tcx> = &'tcx TypePulseCtxtOwner<'tcx>;
pub type TranslationResult<'tcx, T> = Result<T, MirInstantiationError>;

/// Maps Instance to MIR and cache the result.
pub struct TypePulseCtxtOwner<'tcx> {
    tcx: TyCtxt<'tcx>,
    translation_cache: DashMap<DefId, Rc<TranslationResult<'tcx, ir::Body<'tcx>>>>,
    related_item_cache: RelatedItemMap,
    adt_impl_cache: AdtImplMap<'tcx>,
    report_level: ReportLevel,
    optimize_option: bool,
    call_graph_cache: RefCell<Option<Rc<CallGraph<'tcx>>>>, // single call graph in global
    type_check: bool,
}

/// Visit MIR body and returns a TypePulse IR function
/// Check rustc::mir::visit::Visitor for possible visit targets
/// https://doc.rust-lang.org/nightly/nightly-rustc/rustc/mir/visit/trait.Visitor.html
impl<'tcx> TypePulseCtxtOwner<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, 
            report_level: ReportLevel, 
            optimize_option: bool,
            type_check: bool) -> Self {
        TypePulseCtxtOwner {
            tcx,
            translation_cache: DashMap::new(),
            related_item_cache: RelatedFnCollector::collect(tcx),
            adt_impl_cache: create_adt_impl_map(tcx),
            report_level,
            optimize_option,
            call_graph_cache: RefCell::new(None),
            type_check,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn opt_option(&self) -> bool {
        self.optimize_option
    }

    pub fn type_check_option(&self) -> bool {
        self.type_check
    }

    pub fn types_with_related_items(
        &self,
    ) -> impl Iterator<Item = (Option<HirId>, (BodyId, Span))> + '_ {
        (&self.related_item_cache)
            .into_iter()
            .flat_map(|(&k, v)| v.iter().map(move |&body_id| (k, body_id)))
    }

    pub fn translate_body(&self, def_id: DefId) 
            -> (Rc<TranslationResult<'tcx, ir::Body<'tcx>>>, Rc<CallGraph<'tcx>>) {
        let tcx = self.tcx();

        let mut call_graph = if let Some(existing_call_graph) = self.call_graph_cache.borrow().as_ref() {
            (**existing_call_graph).clone()
        } else {
            CallGraph::default()
        };
        
        let result = self.translation_cache.entry(def_id).or_insert_with(|| {
            Rc::new(
                try {
                    let mir_body = Self::find_fn(tcx, def_id)?;

                    self.translate_body_impl(mir_body, &mut call_graph, def_id)?
                },
            )
        });

        // Reuse an existing call_graph from the call_graph_cache if any is available
        {
            let rc_call_graph = Rc::new(call_graph.clone());
            let mut cache = self.call_graph_cache.borrow_mut();
            *cache = Some(rc_call_graph.clone());
        }

        (result.clone(), Rc::new(call_graph))
    }

    fn translate_body_impl(
        &self,
        body: &mir::Body<'tcx>,
        call_graph: &mut CallGraph<'tcx>,
        cur_func_id: DefId,
    ) -> TranslationResult<'tcx, ir::Body<'tcx>> {
        let local_decls = body
            .local_decls
            .iter()
            .map(|local_decl| self.translate_local_decl(local_decl))
            .collect::<Vec<_>>();

        let basic_blocks: Vec<_> = body
            .basic_blocks
            .iter()
            .map(|basic_block| self.translate_basic_block(basic_block))
            .collect::<Result<Vec<_>, _>>()?;

        // we only locate local rather than place
        // e.g., (*_3).field: we would only locate _3
        let mut v = Vec::new();
        for _ in 0..local_decls.len() {
            let mut vv = Vec::new();
            v.push(vv);
        }

        for bb in &basic_blocks {
            for statement in &bb.statements {
                // statement: mir::Statement
                match &statement.kind {
                    StatementKind::Assign(box (lplace, rval)) => {
                        match rval {
                            Rvalue::Cast(cast_kind, op, dest_ty) => {
                                match cast_kind {
                                    CastKind::PtrToPtr | CastKind::Transmute => {
                                        let source_ty = match op {
                                            Operand::Copy(place) | Operand::Move(place) => {
                                                let place_ty = place.ty(&body.local_decls, self.tcx);
                                                place_ty.ty
                                            },
                                            Operand::Constant(box cnst) => {
                                                cnst.literal.ty()
                                            },
                                        };
                                        call_graph.add_type_conversion(cur_func_id, source_ty, *dest_ty);
                                    },
                                    _ => {},
                                }
                                match op {
                                    Operand::Copy(rplace) | Operand::Move(rplace) => {
                                        let id = rplace.local.index();
                                        v[id].push(lplace.local.index());
                                    },
                                    _ => {},
                                }
                            },
                            Rvalue::Use(op)
                            | Rvalue::Repeat(op, _)
                            | Rvalue::ShallowInitBox(op, _) => {
                                match op {
                                    Operand::Copy(rplace) | Operand::Move(rplace) => {
                                        let id = rplace.local.index();
                                        v[id].push(lplace.local.index());
                                    },
                                    _ => {},
                                }
                            },
                            Rvalue::Ref(_, _, rplace)
                            | Rvalue::AddressOf(_, rplace)
                            | Rvalue::Len(rplace)
                            | Rvalue::Discriminant(rplace)
                            | Rvalue::CopyForDeref(rplace) => {
                                let id = rplace.local.index();
                                v[id].push(lplace.local.index());
                            },
                            // Rvalue::Aggregate(box (kind), indexvec) => {
                            //     for op in indexvec.into_iter() {
                            //         match op {
                            //             Operand::Copy(rplace) | Operand::Move(rplace) => {
                            //                 let id = rplace.local.index();
                            //                 v[id].push(lplace.local.index());
                            //             },
                            //             _ => {},
                            //         }
                            //     }
                            // },
                            _ => {},
                        }
                    },
                    _ => {},
                }
            }
            // we also need to handle terminator case
            match &bb.terminator.kind {
                // ir::Terminator
                ir::TerminatorKind::StaticCall {
                    callee_did,
                    callee_substs,
                    ref args,
                    dest,
                } => {
                    
                    // add type_check to functionData in call graph
                    // TyCtxtExtension
                    let ext = self.tcx.ext();
                    let symbol_vec = ext.get_def_path(*callee_did);

                    let mut sym = symbol_vec
                        .iter()
                        .map(|symbol| symbol.as_str())
                        .collect::<Vec<_>>()
                        .join("::");

                    // let mut sym = symbol_vec[ symbol_vec.len() - 1 ].as_str();

                    let final_callee_did = if has_self_parameter(self.tcx, *callee_did) {
                        let resolved_did = if let Some(impl_def_id) = resolve_trait_impl_def_id(self.tcx, *callee_did, callee_substs) {
                            impl_def_id
                        } else {
                            *callee_did
                        };
                        // progress_info!("Find callee as a method: {:?} / {:?}", sym, resolved_did);
                        resolved_did

                        // if is_trait_method(self.tcx, *callee_did) {
                        // } else {
                        //     let resolved_did = resolve_impl_def_id(self.tcx, *callee_did).unwrap_or(*callee_did);
                        //     progress_info!("Find callee as a impl method: {:?} / {:?}", sym, resolved_did);
                        //     resolved_did
                        // }
                    } else {
                        // progress_info!("Find callee as a function: {:?} / {:?}", sym, *callee_did);

                        *callee_did
                    };

                    // Temporary storage for imported_name if needed
                    let mut sym_storage: Option<String> = None;

                    if let Some(imported_name) = find_import_alias(self.tcx, *callee_did) {
                        // progress_info!("    imported as: {:?}", imported_name);
                        sym_storage = Some(imported_name.clone()); // Store the owned String
                        sym = sym_storage.as_deref().unwrap().to_string();     // Update sym to borrow from sym_storage
                    }
                    
                    if sym.contains("align_of") || sym.contains("from_size_align") {
                        // progress_info!("Find align_of in curr function: {:?}", cur_func_id);
                        call_graph.add_type_check(cur_func_id, String::from("align_of"));
                    } else if sym.contains("size_of") {
                        // progress_info!("Find size_of in curr function: {:?}", cur_func_id);
                        call_graph.add_type_check(cur_func_id, String::from("size_of"));
                    } else if sym.contains("unaligned") {
                        // progress_info!("Find unaligned in curr function: {:?}", cur_func_id);
                        call_graph.add_type_check(cur_func_id, String::from("unaligned"));
                    } else if sym.contains("alloc") {
                        call_graph.add_type_check(cur_func_id, String::from("alloc"));
                    } else if sym.contains("TypeId") {
                        call_graph.add_type_check(cur_func_id, String::from("typeid"));
                    } else if sym.contains("Layout") {
                        call_graph.add_type_check(cur_func_id, String::from("Layout"));
                    }

                    for arg in args {
                        // arg: mir::Operand
                        match arg {
                            Operand::Copy(pl) | Operand::Move(pl) => {
                                let id = pl.local.index();
                                v[id].push(dest.local.index());

                                if sym.contains("as_ptr") || sym.contains("as_mut_ptr") {
                                    let source_ty = pl.ty(&body.local_decls, self.tcx()).ty;
                                    let dest_ty = dest.ty(&body.local_decls, self.tcx()).ty;
                                    call_graph.add_type_conversion(cur_func_id, source_ty, dest_ty);
                                }
                            },
                            _ => {},
                        }
                    }

                    // construct call graph
                    // add_caller(&mut self, callee_id: DefId, caller_id: DefId)
                    call_graph.add_caller(final_callee_did, cur_func_id);
                },
                ir::TerminatorKind::Return => {
                    // add return type to function in call_graph
                    call_graph.add_ret_ty(cur_func_id, self.tcx.fn_sig(cur_func_id).skip_binder().output().skip_binder());
                },
                _ => {},
            }
        }

        Ok(ir::Body {
            local_decls,
            original_decls: body.local_decls.to_owned(),
            basic_blocks,
            original: body.to_owned(),
            place_neighbor_list: v,
        })
    }

    fn translate_basic_block(
        &self,
        basic_block: &mir::BasicBlockData<'tcx>,
    ) -> TranslationResult<'tcx, ir::BasicBlock<'tcx>> {
        let statements = basic_block
            .statements
            .iter()
            .map(|statement| statement.clone())
            .collect::<Vec<_>>();

        let terminator = self.translate_terminator(
            basic_block
                .terminator
                .as_ref()
                .expect("Terminator should not be empty at this point"),
        )?;

        Ok(ir::BasicBlock {
            statements,
            terminator,
            is_cleanup: basic_block.is_cleanup,
        })
    }

    fn translate_terminator(
        &self,
        terminator: &mir::Terminator<'tcx>,
    ) -> TranslationResult<'tcx, ir::Terminator<'tcx>> {
        Ok(ir::Terminator {
            kind: match &terminator.kind {
                TerminatorKind::Goto { target } => ir::TerminatorKind::Goto(target.index()),
                TerminatorKind::Return => ir::TerminatorKind::Return,
                TerminatorKind::Call {
                    func: func_operand,
                    args,
                    destination: dest,
                    ..
                } => {
                    if let mir::Operand::Constant(box func) = func_operand {
                        let func_ty = func.literal.ty();
                        match func_ty.kind() {
                            TyKind::FnDef(def_id, callee_substs) => {
                                ir::TerminatorKind::StaticCall {
                                    callee_did: *def_id,
                                    callee_substs,
                                    args: args.clone(),
                                    dest: *dest,
                                }
                            }
                            TyKind::FnPtr(_) => ir::TerminatorKind::FnPtr {
                                value: func.literal.clone(),
                            },
                            _ => panic!("invalid callee of type {:?}", func_ty),
                        }
                    } else {
                        ir::TerminatorKind::Unimplemented("non-constant function call".into())
                    }
                },
                TerminatorKind::Drop { .. } => {
                    // TODO: implement Drop and DropAndReplace terminators
                    ir::TerminatorKind::Unimplemented(
                        format!("TODO terminator: {:?}", terminator).into(),
                    )
                },
                _ => ir::TerminatorKind::Unimplemented(
                    format!("Unknown terminator: {:?}", terminator).into(),
                ),
            },
            original: terminator.clone(),
        })
    }

    fn translate_local_decl(&self, local_decl: &mir::LocalDecl<'tcx>) -> ir::LocalDecl<'tcx> {
        ir::LocalDecl { ty: local_decl.ty }
    }

    /// Try to find MIR function body with def_id.
    fn find_fn(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
    ) -> Result<&'tcx mir::Body<'tcx>, MirInstantiationError> {
        if tcx.is_mir_available(def_id)
            && matches!(
                tcx.hir().body_const_context(def_id.expect_local()),
                None | Some(ConstContext::ConstFn)
            )
        {
            Ok(tcx.optimized_mir(def_id))
        } else {
            debug!(
                "Skipping an item {:?}, no MIR available for this item",
                def_id
            );
            NotAvailable { def_id }.fail()
        }
    }

    // pub fn index_adt_cache(&self, adt_did: &DefId) -> Option<&Vec<(LocalDefId, Ty)>> {
    //     self.adt_impl_cache.get(adt_did)
    // }

    pub fn report_level(&self) -> ReportLevel {
        self.report_level
    }
}