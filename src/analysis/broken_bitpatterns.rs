use rustc_hir::{def_id::DefId, BodyId, Unsafety, def::DefKind};
use rustc_middle::mir::{Operand, StatementKind, Rvalue, CastKind, Place, HasLocalDecls, AggregateKind};
use rustc_middle::mir::RETURN_PLACE;
use rustc_middle::ty::{self, Ty, Instance, ParamEnv, TyKind};
use rustc_span::{Span, DUMMY_SP};

use snafu::{Backtrace, Snafu};
use termcolor::Color;

use crate::graph::GraphTaint;
use crate::prelude::*;
use crate::{
    analysis::{AnalysisKind, IntoReportLevel, ValueChecker, Comparison, get_pointee},
    graph::TaintAnalyzer,
    ir,
    paths::{self, *},
    report::{Report, ReportLevel},
    utils,
    visitor::ContainsUnsafe,
    context::TypePulseCtxt,
    progress_info,
};
use crate::call_graph::CallGraph;

#[derive(Debug, Snafu)]
pub enum BrokenBitPatternsError {
    PushPopBlock { backtrace: Backtrace },
    ResolveError { backtrace: Backtrace },
    InvalidSpan { backtrace: Backtrace },
}

impl AnalysisError for BrokenBitPatternsError {
    fn kind(&self) -> AnalysisErrorKind {
        use BrokenBitPatternsError::*;
        match self {
            PushPopBlock { .. } => AnalysisErrorKind::Unreachable,
            ResolveError { .. } => AnalysisErrorKind::OutOfScope,
            InvalidSpan { .. } => AnalysisErrorKind::Unreachable,
        }
    }
}



pub struct BrokenBitPatternsChecker<'tcx> {
    rcx: TypePulseCtxt<'tcx>,
}

impl<'tcx> BrokenBitPatternsChecker<'tcx> {
    pub fn new(rcx: TypePulseCtxt<'tcx>) -> Self {
        BrokenBitPatternsChecker { rcx }
    }

    pub fn analyze(self) {
        let tcx = self.rcx.tcx();
        let hir_map = tcx.hir();

        // Fist time to iterates all (type, related function) pairs to construct a completed call graph
        for (_ty_hir_id, (body_id, related_item_span)) in self.rcx.types_with_related_items() {

            let body_did = hir_map.body_owner_def_id(body_id).to_def_id();
            
            // progress_info!("Phase 1: Call Graph - BrokenBitPatternChecker::analyze({})", 
            //             tcx.def_path_str(body_did)
            // );

            self.rcx.translate_body(body_did);
        }

        // Iterates all (type, related function) pairs
        for (_ty_hir_id, (body_id, related_item_span)) in self.rcx.types_with_related_items() {
            let f_def_id = hir_map.body_owner_def_id(body_id).to_def_id();

            // progress_info!("Phase 1: Detection - BrokenBitPatternChecker::analyze({})", 
            //             tcx.def_path_str(f_def_id)
            // );

            // based on function itself
            let f_visible = utils::check_visibility(tcx, f_def_id);

            // if function is public, then we still need to check whether it is method and self
            // if function is private, we just need to pass private
            // visible && ty_visible
            let ty_visible = if utils::has_self_parameter(tcx, f_def_id) {
                if let Some(self_ty) = utils::get_method_self_ty(tcx, f_def_id) {
                    utils::check_ty_visibility(tcx, self_ty)
                } else {
                    false
                }
            } else {
                f_visible
            };

            let visible = f_visible && ty_visible;
            
            if let Some(status) = inner::BrokenBitPatternsBodyAnalyzer::analyze_body(self.rcx, body_id, visible)
            {
                let behavior_flag = status.behavior_flag();
                if !behavior_flag.is_empty()
                    && behavior_flag.report_level(visible) >= self.rcx.report_level()
                {
                    // progress_info!("find the bug with behavior_flag: {:?}", behavior_flag);
                    let mut color_span = unwrap_or!(
                        utils::ColorSpan::new(tcx, related_item_span).context(InvalidSpan) => continue
                    );

                    // for &span in status.strong_bypass_spans() {
                    //     color_span.add_sub_span(Color::Red, span);
                    // }

                    // for &span in status.weak_bypass_spans() {
                    //     color_span.add_sub_span(Color::Yellow, span);
                    // }

                    // for &span in status.unresolvable_generic_function_spans() {
                    //     color_span.add_sub_span(Color::Cyan, span);
                    // }

                    // for &span in status.plain_deref_spans() {
                    //     color_span.add_sub_span(Color::Blue, span);
                    // }
                    
                    for &span in status.ty_conv_spans() {
                        color_span.add_sub_span(Color::Green, span);
                    }

                    typepulse_report(Report::with_color_span(
                        tcx,
                        behavior_flag.report_level(visible),
                        AnalysisKind::BrokenBitPatterns(behavior_flag),
                        format!(
                            "Potential broken bit patterns issue in `{}`",
                            tcx.def_path_str(hir_map.body_owner_def_id(body_id).to_def_id())
                        ),
                        &color_span,
                    ))
                } else {
                    // progress_info!("bug not found");
                }
            }
        }
    }
}

mod inner {
    use super::*;

    #[derive(Debug, Default)]
    pub struct BrokenBitPatternsStatus {
        strong_bypasses: Vec<Span>,
        weak_bypasses: Vec<Span>,
        plain_deref: Vec<Span>,
        unresolvable_generic_functions: Vec<Span>,
        ty_convs: Vec<Span>,
        creation: Vec<Span>,
        behavior_flag: BehaviorFlag,
    }

    impl BrokenBitPatternsStatus {
        pub fn behavior_flag(&self) -> BehaviorFlag {
            self.behavior_flag
        }

        pub fn strong_bypass_spans(&self) -> &Vec<Span> {
            &self.strong_bypasses
        }

        pub fn weak_bypass_spans(&self) -> &Vec<Span> {
            &self.weak_bypasses
        }

        pub fn plain_deref_spans(&self) -> &Vec<Span> {
            &self.plain_deref
        }

        pub fn unresolvable_generic_function_spans(&self) -> &Vec<Span> {
            &self.unresolvable_generic_functions
        }

        pub fn ty_conv_spans(&self) -> &Vec<Span> {
            &self.ty_convs
        }
    }

    pub struct BrokenBitPatternsBodyAnalyzer<'a, 'tcx> {
        rcx: TypePulseCtxt<'tcx>,
        body: &'a ir::Body<'tcx>,
        param_env: ParamEnv<'tcx>,
        status: BrokenBitPatternsStatus,
    }

    impl<'a, 'tcx> BrokenBitPatternsBodyAnalyzer<'a, 'tcx> {
        fn new(rcx: TypePulseCtxt<'tcx>, param_env: ParamEnv<'tcx>, body: &'a ir::Body<'tcx>) -> Self {
            BrokenBitPatternsBodyAnalyzer {
                rcx,
                body,
                param_env,
                status: Default::default(),
            }
        }

        pub fn analyze_body(rcx: TypePulseCtxt<'tcx>, body_id: BodyId, visible: bool) -> Option<BrokenBitPatternsStatus> {
            let hir_map = rcx.tcx().hir();
            let body_did = hir_map.body_owner_def_id(body_id).to_def_id();

            let item_kind = rcx.tcx().def_kind(body_did);
            if !matches!(item_kind, DefKind::Fn | DefKind::AssocFn) {
                return None;
            }

            if rcx.tcx().ext().match_def_path(
                body_did,
                &["typepulse_paths_discovery", "PathsDiscovery", "discover"],
            ) {
                // progress_info!("special case required");
                // Special case for paths discovery
                trace_calls_in_body(rcx, body_did);
                None
            } else if ContainsUnsafe::contains_unsafe(rcx.tcx(), body_id) {
                let fn_sig = rcx.tcx().fn_sig(body_did).skip_binder();
                if let Unsafety::Unsafe = fn_sig.unsafety() {
                    // progress_info!("The function is unsafe");
                    None
                } else {
                    // progress_info!("This function contains unsafe block");
                    let (rc_body, rc_call_graph) = rcx.translate_body(body_did);
                    match rc_body.as_ref() {
                        Err(e) => {
                            // MIR is not available for def - log it and continue
                            e.log();
                            None
                        }
                        Ok(body) => {
                            let param_env = rcx.tcx().param_env(body_did);
                            let body_analyzer = BrokenBitPatternsBodyAnalyzer::new(rcx, param_env, body);

                            let mut tconv_source: Vec<usize> = Vec::new();
                            let mut tconv_ty: Vec<Ty<'tcx>> = Vec::new();

                            Some(body_analyzer.analyze(tconv_source, tconv_ty, rc_call_graph.as_ref(), visible, body_did))
                        }
                    }
                }
            } else {
                Some(Default::default())
            }
        }

        fn analyze(mut self, 
                mut tconv_source: Vec<usize>, 
                mut tconv_ty: Vec<Ty<'tcx>>, 
                call_graph: &CallGraph<'tcx>, 
                visible: bool, 
                cur_func_id: DefId) -> BrokenBitPatternsStatus {

            let has_static_bound = utils::has_static_bound(self.rcx.tcx(), cur_func_id);

            let loc_decls = self.body.local_decls();
            let mut taint_analyzer = TaintAnalyzer::new(self.body);

            let ext = self.rcx.tcx().ext();

            let cur_fdata = if call_graph.functions.contains_key(&cur_func_id) {
                // progress_info!("Phase 2 - Find curr function in call graph");
                Some(&call_graph.functions[&cur_func_id])
            } else {
                // progress_info!("Phase 2 - Not find curr function in call graph");
                None
            };
            
            // used for detecting type conversion before utf8_checked
            let mut pre_conv_utf8_unchecked: bool = false;

            for bb in self.body.basic_blocks() {
                'st_iter: for statement in &bb.statements {
                    // statement here is mir::Statement without translation
                    // while iterating statements, we plan to mark ty conv as source / plain deref as sink
                    // progress_info!("statement: {:?}", statement);
                    match &statement.kind {
                        StatementKind::Assign(box (lplace, rval)) => {
                            // rhs
                            match rval {
                                Rvalue::Cast(cast_kind, op, to_ty) => {
                                    match cast_kind {
                                        CastKind::PtrToPtr => {
                                            // progress_info!("cast::ptr-ptr");
                                            let f_ty = get_ty_from_op(self.body, self.rcx, &op);
                                            match f_ty {
                                                Ok(from_ty) => {
                                                    let symbol_vec = if let Some(ty_def_id) = utils::extract_ty_def_id(from_ty) {
                                                        // use def_id to get symbol name of ty
                                                        ext.get_def_path(ty_def_id)
                                                    } else {
                                                        Vec::new()
                                                    };

                                                    let to_symbol_vec = if let Some(ty_def_id) = utils::extract_ty_def_id(*to_ty) {
                                                        ext.get_def_path(ty_def_id)
                                                    } else {
                                                        Vec::new()
                                                    };
                                                    

                                                    let vc = ValueChecker::new(self.rcx, self.param_env, from_ty, *to_ty);
                                                    let value_status = vc.get_val_status();

                                                    // progress_info!("value_status: {:?}", value_status);

                                                    let pl = get_place_from_op(&op);
                                                    match pl {
                                                        Ok(place) => {
                                                            let id = place.local.index();

                                                            let mut pre_conv = false;
                                                            if !tconv_source.is_empty() {
                                                                for idx in 0..tconv_source.len() {
                                                                    let conv_id = tconv_source[idx];
                                                                    // to_ty in previous type conversion
                                                                    let conv_ty = tconv_ty[idx];
                                                                    // progress_info!("conv_ty: {:?}", conv_ty);
                                                                    if taint_analyzer.is_reachable(conv_id, id) 
                                                                    && (conv_ty == get_pointee(from_ty)) 
                                                                    {
                                                                        pre_conv = true;
                                                                        break;
                                                                    }
                                                                }
                                                            }

                                                            // progress_info!("has previous type conversion: {:?}, visible: {:?}", pre_conv, visible);

                                                            // if A could be generic type or composite type, and B is primitive type, taint as source
                                                            match value_status {
                                                                Comparison::Less => {
                                                                    if visible {
                                                                        // progress_info!("Visible + Less + Cast");
                                                                        taint_analyzer.mark_at_once(id, &BehaviorFlag::CAST);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);

                                                                        self.status
                                                                            .creation
                                                                            .push(statement.source_info.span);
                                                                    } else if pre_conv && !visible {
                                                                        for s in to_symbol_vec {
                                                                            if s.as_str().contains("c_void") {
                                                                                // the data passed from libc is already aligned
                                                                                continue 'st_iter;
                                                                            }
                                                                        }
                                                                        if self.rcx.type_check_option() {
                                                                            // progress_info!("has prev ty conv but not visible");
                                                                            // first the current type might not be the real source type
                                                                            // e.g., we get *const u8 as from_ty
                                                                            // however, it might come from *mutableBuffer.as_ptr()
                                                                            // in this case, we need to find the true source type which is mutableBuffer
                                                                            let pointee_from_ty = if let Some(fdata) = cur_fdata {
                                                                                if let Some(source_list) = fdata.type_conversions.get_constructor_source(from_ty) {
                                                                                    if source_list.len() != 0 {
                                                                                        get_pointee(source_list[0])
                                                                                    } else {
                                                                                        get_pointee(from_ty)
                                                                                    }
                                                                                } else {
                                                                                    get_pointee(from_ty)
                                                                                }
                                                                            } else {
                                                                                get_pointee(from_ty)
                                                                            };
                                                                            // progress_info!("pointee_from_ty: {:?}", pointee_from_ty);

                                                                            match pointee_from_ty.kind() {
                                                                                TyKind::Array(ety, _) | TyKind::Slice(ety) => {
                                                                                    if ety.is_numeric() {
                                                                                        taint_analyzer.mark_at_once(id, &BehaviorFlag::CAST);
                                                                                        self.status
                                                                                            .ty_convs
                                                                                            .push(bb.terminator.original.source_info.span);
                                    
                                                                                        self.status
                                                                                            .creation
                                                                                            .push(bb.terminator.original.source_info.span);
                                                                                        break;
                                                                                    }
                                                                                },
                                                                                _ => {},
                                                                            }
                                                                            
                                                                            let constructor_id_list = call_graph.retmap.get_func_by_ret_ty(pointee_from_ty);
                                                                            // progress_info!("construct: {:?}", constructor_id_list);
                                                                            if constructor_id_list.len() != 0 {
                                                                                let mut is_caller_checked = false;
                                                                                for constructor_defid in constructor_id_list {
                                                                                    let constructor_typecheck = &call_graph.functions[&constructor_defid].type_check;
                                                                                    // progress_info!("Constructor has type check: {:?}", constructor_typecheck);
                                                                                    if constructor_typecheck.contains("align_of") {
                                                                                        is_caller_checked |= true;
                                                                                    } else {
                                                                                        is_caller_checked |= false;
                                                                                    }
                                                                                }

                                                                                if !is_caller_checked {
                                                                                    taint_analyzer.mark_at_once(id, &BehaviorFlag::CAST);
                                                                                    self.status
                                                                                        .ty_convs
                                                                                        .push(statement.source_info.span);

                                                                                    self.status
                                                                                        .creation
                                                                                        .push(statement.source_info.span);
                                                                                }
                                                                                
                                                                            }
                                                                        }
                                                                    } 
                                                                    // else if !pre_conv && !visible {
                                                                    //     progress_info!("no prev ty conv and not visible");

                                                                    //     if to_ty.to_string().contains("c_void") {
                                                                    //         continue 'st_iter;
                                                                    //     }

                                                                    //     if self.rcx.type_check_option() {
                                                                    //         let pointee_from_ty = get_pointee(from_ty);

                                                                    //         let constructor_id_list = call_graph.retmap.get_func_by_ret_ty(pointee_from_ty);
                                                                    //         progress_info!("construct: {:?}", constructor_id_list);
                                                                    //         if constructor_id_list.len() != 0 {
                                                                    //             let mut is_caller_checked = false;
                                                                    //             for constructor_defid in constructor_id_list {
                                                                    //                 let constructor_typecheck = &call_graph.functions[&constructor_defid].type_check;
                                                                    //                 progress_info!("Constructor has type check: {:?}", constructor_typecheck);
                                                                    //                 if constructor_typecheck.contains("align_of") {
                                                                    //                     is_caller_checked |= true;
                                                                    //                 } else {
                                                                    //                     is_caller_checked |= false;
                                                                    //                 }
                                                                    //             }

                                                                    //             if !is_caller_checked {
                                                                    //                 taint_analyzer.mark_at_once(id, &BehaviorFlag::CAST);
                                                                    //                 self.status
                                                                    //                     .ty_convs
                                                                    //                     .push(statement.source_info.span);

                                                                    //                 self.status
                                                                    //                     .creation
                                                                    //                     .push(statement.source_info.span);
                                                                    //             }
                                                                                
                                                                    //         }
                                                                    //     }
                                                                    // }
                                                                },
                                                                Comparison::Greater | Comparison::NoideaG => {
                                                                    if to_ty.is_mutable_ptr() && visible {
                                                                        // from immutable to mutable
                                                                        progress_info!("Mismatched Scope Bug: Waiting type to be mutated as invalid type...");
                                                                        if taint_analyzer.is_reachable(id, 0) {
                                                                            let arg_count = self.body.arg_cnt();
                                                                            for idx in 1..arg_count + 1 {
                                                                                match loc_decls[idx.into()].ty.kind() {
                                                                                    TyKind::RawPtr(..) | TyKind::Ref(..) | TyKind::Param(..) => {
                                                                                        taint_analyzer.mark_at_once(id, &BehaviorFlag::CAST);
                                                                                        self.status
                                                                                            .ty_convs
                                                                                            .push(statement.source_info.span);

                                                                                        self.status
                                                                                            .creation
                                                                                            .push(statement.source_info.span);
                                                                                    },
                                                                                    _ => {},
                                                                                }
                                                                            }
                                                                        }
                                                                    } 
                                                                    else if to_ty.is_mutable_ptr() {
                                                                        if self.rcx.type_check_option() {
                                                                            let pointee_from_ty = get_pointee(from_ty);
                                                                            let constructor_id_list = call_graph.retmap.get_func_by_ret_ty(pointee_from_ty);
                                                                            // progress_info!("construct: {:?}", constructor_id_list);
                                                                            if (constructor_id_list.len() != 0) && taint_analyzer.is_reachable(id, 0) {
                                                                                taint_analyzer.mark_at_once(id, &BehaviorFlag::CAST);
                                                                                self.status
                                                                                   .ty_convs
                                                                                    .push(statement.source_info.span);

                                                                                self.status
                                                                                    .creation
                                                                                    .push(statement.source_info.span);
                                                                            }
                                                                        }
                                                                    }
                                                                },
                                                                _ => {
                                                                    tconv_source.push(id);
                                                                    tconv_ty.push(get_pointee(*to_ty));
                                                                },
                                                            }
                                                        },
                                                        Err(_e) => {
                                                            // progress_info!("Can't get place from the cast operand");
                                                        },
                                                    }
                                                },
                                                Err(_e) => {
                                                    // progress_info!("Can't get ty from the cast place");
                                                },
                                            }
                                        },
                                        CastKind::Transmute => {
                                            let f_ty = get_ty_from_op(self.body, self.rcx, &op);
                                            match f_ty {
                                                Ok(from_ty) => {
                                                    if !is_ptr_ty(from_ty, *to_ty) {
                                                        continue;
                                                    }

                                                    let symbol_vec = if let Some(ty_def_id) = utils::extract_ty_def_id(from_ty) {
                                                        // use def_id to get symbol name of ty
                                                        ext.get_def_path(ty_def_id)
                                                    } else {
                                                        Vec::new()
                                                    };

                                                    // progress_info!("transmute::ptr-ptr");
                                                    let vc = ValueChecker::new(self.rcx, self.param_env, from_ty, *to_ty);
                                                    let value_status = vc.get_val_status();

                                                    let pl = get_place_from_op(&op);
                                                    match pl {
                                                        Ok(place) => {
                                                            let id = place.local.index();

                                                            let mut pre_conv: bool = false;
                                                            if !tconv_source.is_empty() {
                                                                for idx in 0..tconv_source.len() {
                                                                    let conv_id = tconv_source[idx];
                                                                    // to_ty in previous type conversion
                                                                    let conv_ty = tconv_ty[idx];
                                                                    if taint_analyzer.is_reachable(conv_id, id) &&
                                                                        (conv_ty == get_pointee(from_ty)) {
                                                                        pre_conv = true;
                                                                        break;
                                                                    }
                                                                }
                                                            }

                                                            match value_status {
                                                                // make sure it is not kind of bug 1
                                                                Comparison::Less => {
                                                                    if !pre_conv {
                                                                        taint_analyzer.mark_at_once(id, &BehaviorFlag::TRANSMUTE);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);

                                                                        self.status
                                                                            .creation
                                                                            .push(statement.source_info.span);
                                                                        // progress_info!("cast leads to ub in this statement");
                                                                    }
                                                                },
                                                                Comparison::Greater => {
                                                                    if to_ty.is_mutable_ptr() && visible {
                                                                        for s in symbol_vec {
                                                                            if s.as_str().contains("libc") {
                                                                                // the data passed from libc is already aligned
                                                                                continue 'st_iter;
                                                                            }
                                                                        }
                                                                        if !pre_conv {
                                                                            taint_analyzer.mark_at_once(id, &BehaviorFlag::TRANSMUTE);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
        
                                                                            self.status
                                                                                .creation
                                                                                .push(statement.source_info.span);
                                                                            // progress_info!("cast leads to ub in this statement");
                                                                        }
                                                                    } else if to_ty.is_mutable_ptr() && has_static_bound {
                                                                        taint_analyzer.mark_at_once(id, &BehaviorFlag::TRANSMUTE);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);

                                                                        self.status
                                                                            .creation
                                                                            .push(statement.source_info.span);
                                                                    }
                                                                },
                                                                _ => {
                                                                    tconv_source.push(id);
                                                                    tconv_ty.push(*to_ty);
                                                                },
                                                            }
                                                        },
                                                        Err(_e) => {
                                                            // progress_info!("Can't get place from the transmute operand");
                                                        },
                                                    }
                                                },
                                                Err(_e) => {
                                                    // progress_info!("Can't get ty from the transmute place");
                                                },
                                            }
                                        },
                                        _ => (),
                                    }
                                },
                                _ => {},
                            }
                        },
                        _ => {},
                    }

                }

                match bb.terminator.kind {
                    // progress_info!("terminator: {:?}", terminator);
                    ir::TerminatorKind::StaticCall {
                        callee_did,
                        callee_substs,
                        ref args,
                        dest,
                        ..
                    } => {
                        let tcx = self.rcx.tcx();
                        // TyCtxtExtension
                        let ext = tcx.ext();
                        // Check for lifetime bypass
                        let symbol_vec = ext.get_def_path(callee_did);
                        // progress_info!("terminator with symbol: {:?}", symbol_vec);
                        let sym = symbol_vec[ symbol_vec.len() - 1 ].as_str();

                        // progress_info!("call f: {:?}", sym);

                        if sym.contains("alloc") {
                            let id = dest.local.index();
                            taint_analyzer
                                .clear_source(id);
                        } else if sym.contains("as_bytes") {
                            // str.as_bytes()
                            for arg in args {
                                match arg {
                                    Operand::Copy(pl) | Operand::Move(pl) => {
                                        let local = pl.local;
                                        let local_decl = &self.body.original_decls[local];
                                        let pointee_ty = get_pointee(local_decl.ty);
                                        if pointee_ty.is_str() {
                                            pre_conv_utf8_unchecked = true;
                                        }
                                    },
                                    _ => {},
                                }
                            }
                        } else if sym.contains("from_utf8_unchecked") {
                            // progress_info!("Find str from utf8 unchecked");
                            let id = dest.local.index();

                            for arg in args {
                                match arg {
                                    Operand::Copy(pl) | Operand::Move(pl) => {
                                        let local = pl.local;
                                        let local_decl = &self.body.original_decls[local];
                                        let pointee_ty = get_pointee(local_decl.ty);
                                        match pointee_ty.kind() {
                                            TyKind::Array(ety, _) | TyKind::Slice(ety) => {
                                                if ety.is_numeric() && visible && !pre_conv_utf8_unchecked {
                                                    // progress_info!("Visible + Less + utf8unchecked");
                                                    taint_analyzer.mark_at_once(id, &BehaviorFlag::FUNC);
                                                    self.status
                                                        .ty_convs
                                                        .push(bb.terminator.original.source_info.span);

                                                    self.status
                                                        .creation
                                                        .push(bb.terminator.original.source_info.span);
                                                    break;
                                                }
                                            },
                                            TyKind::Adt(adt_def, substs) => {
                                                let mut all_field_numeric = true;
                                                for field in adt_def.all_fields() {
                                                    let field_ty = field.ty(tcx, substs);
                                    
                                                    if !field_ty.is_numeric() {
                                                        all_field_numeric = false;
                                                    }
                                                }

                                                if all_field_numeric && visible && !pre_conv_utf8_unchecked {
                                                    // progress_info!("Visible + Less + utf8unchecked");
                                                    taint_analyzer.mark_at_once(id, &BehaviorFlag::FUNC);
                                                    self.status
                                                        .ty_convs
                                                        .push(bb.terminator.original.source_info.span);

                                                    self.status
                                                        .creation
                                                        .push(bb.terminator.original.source_info.span);
                                                    break;
                                                }
                                            },
                                            _ => {},
                                        }
                                    },
                                    _ => {},
                                }
                            }
                        } else if sym.contains("from_utf8") {
                            // str::from_utf8
                            pre_conv_utf8_unchecked = true;
                        } else if sym.contains("as_ptr") || sym.contains("as_mut_ptr") {
                            // progress_info!("find as pointer call");
                            let id = dest.local.index();
                            tconv_source.push(id);
                            tconv_ty.push(get_pointee(dest.ty(self.body, self.rcx.tcx()).ty));
                        }
                    },
                    ir::TerminatorKind::Return => {
                        // _0 is always considered as return value
                        let return_pl0 = self.body.local_decls().get(RETURN_PLACE);
                        if return_pl0.is_some() {
                            match return_pl0.unwrap().ty.kind() {
                                TyKind::Ref(..) => {
                                    // taint_analyzer.mark_sink(0);
                                    // self.status
                                    //     .plain_deref
                                    //     .push(terminator.original.source_info.span);
                                },
                                _ => {},
                            }
                        }
                    },
                    _ => {},
                }
            }

            self.status.behavior_flag = taint_analyzer.propagate();
            self.status
        }
    }

    fn trace_calls_in_body<'tcx>(rcx: TypePulseCtxt<'tcx>, body_def_id: DefId) {
        warn!("Paths discovery function has been detected");
        let (rc_body, rc_call_graph) = rcx.translate_body(body_def_id);
        if let Ok(body) = rc_body.as_ref() {
            for terminator in body.terminators() {
                match terminator.kind {
                    ir::TerminatorKind::StaticCall { callee_did, .. } => {
                        let ext = rcx.tcx().ext();
                        println!(
                            "{}",
                            ext.get_def_path(callee_did)
                                .iter()
                                .fold(String::new(), |a, b| a + " :: " + &*b.as_str())
                        );
                    }
                    _ => (),
                }
            }
        }
    }
}

// check whether both from_ty and to_ty are pointer types
fn is_ptr_ty<'tcx>(from_ty: Ty<'tcx>, to_ty: Ty<'tcx>) -> bool {
    // (from_ty|to_ty) needs to be raw pointer or reference
    let is_fty_ptr = if let ty::RawPtr(_) = from_ty.kind() {
        true
    } else if let ty::Ref(..) = from_ty.kind() {
        true
    } else {
        false
    };
    let is_tty_ptr = if let ty::RawPtr(_) = to_ty.kind() {
        true
    } else if let ty::Ref(..) = to_ty.kind() {
        true
    } else {
        false
    };
    (is_fty_ptr & is_tty_ptr)
}

fn get_place_from_op<'tcx>(op: &Operand<'tcx>) -> Result<Place<'tcx>, &'static str> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            Ok(*place)
        },
        _ => { Err("Can't get place from operand") },
    }
}

fn get_ty_from_op<'tcx>(bd: &ir::Body<'tcx>, rcx: TypePulseCtxt<'tcx>, op: &Operand<'tcx>) -> Result<Ty<'tcx>, &'static str> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            Ok(place.ty(bd, rcx.tcx()).ty)
        },
        Operand::Constant(box cnst) => {
            Ok(cnst.ty())
        },
        _ => { Err("Can't get ty from place") },
    }
}

// Type Conversion Kind.
// Used to associate each broken bit patterns bug report with its cause.
bitflags! {
    #[derive(Default)]
    pub struct BehaviorFlag: u16 {
        const CAST = 0b00000001;
        const TRANSMUTE = 0b00000010;
        const FUNC = 0b00000100;
    }
}

impl IntoReportLevel for BehaviorFlag {
    fn report_level(&self, visibility: bool) -> ReportLevel {
        use BehaviorFlag as Flag;

        let high = Flag::CAST | Flag::TRANSMUTE;
        //let med = Flag::READ_FLOW | Flag::COPY_FLOW | Flag::WRITE_FLOW;

        // if !(*self & high).is_empty() {
        //     ReportLevel::Error
        // } else if !(*self & med).is_empty() {
        //     ReportLevel::Warning
        // } else {
        //     ReportLevel::Info
        // }

        ReportLevel::Error
    }
}

impl GraphTaint for BehaviorFlag {
    fn is_empty(&self) -> bool {
        self.is_all()
    }

    fn contains(&self, taint: &Self) -> bool {
        self.contains(*taint)
    }

    fn join(&mut self, taint: &Self) {
        *self |= *taint;
    }
}
