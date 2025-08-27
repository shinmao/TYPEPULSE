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
    analysis::{AnalysisKind, IntoReportLevel, LayoutChecker, Comparison},
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
use crate::analysis::get_pointee;
use std::cell::RefCell;

#[derive(Debug, Snafu)]
pub enum BrokenLayoutError {
    PushPopBlock { backtrace: Backtrace },
    ResolveError { backtrace: Backtrace },
    InvalidSpan { backtrace: Backtrace },
}

impl AnalysisError for BrokenLayoutError {
    fn kind(&self) -> AnalysisErrorKind {
        use BrokenLayoutError::*;
        match self {
            PushPopBlock { .. } => AnalysisErrorKind::Unreachable,
            ResolveError { .. } => AnalysisErrorKind::OutOfScope,
            InvalidSpan { .. } => AnalysisErrorKind::Unreachable,
        }
    }
}

pub struct BrokenLayoutChecker<'tcx> {
    rcx: TypePulseCtxt<'tcx>,
}

impl<'tcx> BrokenLayoutChecker<'tcx> {
    pub fn new(rcx: TypePulseCtxt<'tcx>) -> Self {
        BrokenLayoutChecker { rcx }
    }

    pub fn analyze(self) {
        let tcx = self.rcx.tcx();
        let hir_map = tcx.hir();

        // Fist time to iterates all (type, related function) pairs to construct a completed call graph
        for (_ty_hir_id, (body_id, related_item_span)) in self.rcx.types_with_related_items() {

            let body_did = hir_map.body_owner_def_id(body_id).to_def_id();
            
            // progress_info!("Phase 1: Call Graph - BrokenLayoutChecker::analyze({})", 
            //             tcx.def_path_str(body_did)
            // );
            
            self.rcx.translate_body(body_did);
        } 
        

        // Second time to iterates all (type, related function) pairs to perform detection
        for (_ty_hir_id, (body_id, related_item_span)) in self.rcx.types_with_related_items() {
            
            // print the funciton name of current body
            // progress_info!("Phase 2: Detection - BrokenLayoutChecker::analyze({})", 
            //             tcx.def_path_str(hir_map.body_owner_def_id(body_id).to_def_id())
            // );


            if let Some(status) = inner::BrokenLayoutBodyAnalyzer::analyze_body(self.rcx, body_id)
            {
                let behavior_flag = status.behavior_flag();
                if !behavior_flag.is_empty()
                    //&& behavior_flag.report_level() >= self.rcx.report_level()
                {
                    // progress_info!("find the bug with behavior_flag: {:?}", behavior_flag);
                    let mut color_span = unwrap_or!(
                        utils::ColorSpan::new(tcx, related_item_span).context(InvalidSpan) => continue
                    );

                    for &span in status.strong_bypass_spans() {
                        color_span.add_sub_span(Color::Red, span);
                    }

                    for &span in status.weak_bypass_spans() {
                        color_span.add_sub_span(Color::Yellow, span);
                    }

                    for &span in status.unresolvable_generic_function_spans() {
                        color_span.add_sub_span(Color::Cyan, span);
                    }

                    for &span in status.plain_deref_spans() {
                        color_span.add_sub_span(Color::Blue, span);
                    }
                    
                    for &span in status.ty_conv_spans() {
                        color_span.add_sub_span(Color::Green, span);
                    }

                    typepulse_report(Report::with_color_span(
                        tcx,
                        behavior_flag.report_level(true),
                        AnalysisKind::BrokenLayout(behavior_flag),
                        format!(
                            "Potential broken layout issue in `{}`",
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
    pub struct BrokenLayoutStatus {
        strong_bypasses: Vec<Span>,
        weak_bypasses: Vec<Span>,
        plain_deref: Vec<Span>,
        unresolvable_generic_functions: Vec<Span>,
        ty_convs: Vec<Span>,
        behavior_flag: BehaviorFlag,
    }

    impl BrokenLayoutStatus {
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

    pub struct BrokenLayoutBodyAnalyzer<'a, 'tcx> {
        rcx: TypePulseCtxt<'tcx>,
        body: &'a ir::Body<'tcx>,
        param_env: ParamEnv<'tcx>,
        status: BrokenLayoutStatus,
    }

    impl<'a, 'tcx> BrokenLayoutBodyAnalyzer<'a, 'tcx> {
        fn new(rcx: TypePulseCtxt<'tcx>, param_env: ParamEnv<'tcx>, body: &'a ir::Body<'tcx>) -> Self {
            BrokenLayoutBodyAnalyzer {
                rcx,
                body,
                param_env,
                status: Default::default(),
            }
        }

        pub fn analyze_body(rcx: TypePulseCtxt<'tcx>, body_id: BodyId) -> Option<BrokenLayoutStatus> {
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
                            let body_analyzer = BrokenLayoutBodyAnalyzer::new(rcx, param_env, body);
                            Some(body_analyzer.analyze(rc_call_graph.as_ref(), body_did))
                        }
                    }
                }
            } else {
                // We don't perform interprocedural analysis from the safe function not including unsafe block
                // thus safe functions are considered safe
                Some(Default::default())
            }
        }

        fn analyze(mut self, call_graph: &CallGraph<'tcx>, cur_func_id: DefId) -> BrokenLayoutStatus {
            // progress_info!("Curr function has id: {:?}", cur_func_id);

            let mut taint_analyzer = TaintAnalyzer::new(self.body);

            // based on function itself
            let f_visible = utils::check_visibility(self.rcx.tcx(), cur_func_id);
            // progress_info!("f_visible: {:?}", f_visible);

            // if function is public, then we still need to check whether it is method and self
            // if function is private, we just need to pass private
            // visible && ty_visible
            let ty_visible = if utils::has_self_parameter(self.rcx.tcx(), cur_func_id) {
                // progress_info!("Found self parameter");
                if let Some(self_ty) = utils::get_method_self_ty(self.rcx.tcx(), cur_func_id) {
                    utils::check_ty_visibility(self.rcx.tcx(), self_ty)
                } else {
                    false
                }
            } else {
                f_visible
            };
            // progress_info!("ty_visible: {:?}", ty_visible);

            let is_visible = f_visible && ty_visible;

            // let is_visible = utils::check_visibility(self.rcx.tcx(), cur_func_id);
            // progress_info!("The function is visible: {:?}", is_visible);

            // TyCtxt
            let ext = self.rcx.tcx().ext();
            
            // This flag is control-flow sensitive and used in single function
            // will be checked before type conversion
            // ie. pre-condition check
            let mut type_checked = false;
            // this is used for exception case
            let mut optional_type_checked = false;
            // post type check
            let mut post_type_checked = false;

            let cur_fdata = if call_graph.functions.contains_key(&cur_func_id) {
                // progress_info!("Phase 2 - Find curr function in call graph");
                Some(&call_graph.functions[&cur_func_id])
            } else {
                // progress_info!("Phase 2 - Not find curr function in call graph");
                None
            };

            for bb in self.body.basic_blocks() {
                'st_iter: for statement in &bb.statements {
                    // statement here is mir::Statement without translation
                    // while iterating statements, we plan to mark ty conv as source / plain deref as sink
                    // progress_info!("{:?}", statement);
                    match &statement.kind {
                        StatementKind::Assign(box (lplace, rval)) => {
                            // lhs could also contains deref operation
                            if lplace.is_indirect() {
                                // contains deref projection
                                // progress_info!("warn::deref on place:{}", lplace.local.index());
                                if post_type_checked {
                                    // continue 'st_iter;
                                }
                                taint_analyzer.mark_sink(lplace.local.index());
                                self.status
                                    .plain_deref
                                    .push(statement.source_info.span);
                            }
                            // rhs
                            match rval {
                                Rvalue::Cast(cast_kind, op, to_ty) => {
                                    match cast_kind {
                                        CastKind::PtrToPtr => {
                                            // progress_info!("cast::ptr-ptr");
                                            let f_ty = get_ty_from_op(self.body, self.rcx, &op);

                                            match f_ty {
                                                Ok(from_ty) => {
                                                    if let Some(ty_def_id) = utils::extract_ty_def_id(from_ty) {
                                                        // use def_id to get symbol name of ty
                                                        let symbol_vec = ext.get_def_path(ty_def_id);
                                                        for s in symbol_vec {
                                                            if s.as_str().contains("libc") {
                                                                // the data passed from libc is already aligned
                                                                continue 'st_iter;
                                                            }
                                                        }
                                                    }

                                                    let mut constructor_list = Vec::new();

                                                    // check the potential type constructor
                                                    if !is_visible && self.rcx.type_check_option() {
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

                                                        for constructor_id in call_graph.retmap.get_func_by_ret_ty(pointee_from_ty) {
                                                            // progress_info!("constructor id: {:?}", constructor_id);
                                                            constructor_list.push(constructor_id);
                                                            if let Some(source_list) = 
                                                                call_graph.functions[&constructor_id]
                                                                .type_conversions
                                                                .get_constructor_source(pointee_from_ty) {
                                                                    if source_list.len() != 0 {
                                                                        // progress_info!("no ty conv in callers");
                                                                        continue 'st_iter;
                                                                    }
                                                            }
                                                        }
                                                    }

                                                    let lc = LayoutChecker::new(self.rcx, self.param_env, from_ty, *to_ty);
                                                    let fty = lc.get_from_ty();
                                                    let tty = lc.get_to_ty();
                                                    let align_status = lc.get_align_status();

                                                    let (is_from_dyn, is_to_dyn) = lc.is_from_to_dyn();
                                                    if is_from_dyn | is_to_dyn {
                                                        continue;
                                                    }

                                                    if fty.to_string().contains("TypeId") || tty.to_string().contains("TypeId") {
                                                        continue 'st_iter;
                                                    }

                                                    let pl = get_place_from_op(&op);
                                                    match pl {
                                                        Ok(place) => {
                                                            let id = place.local.index();
                                                            // progress_info!("align_status: {:?}", align_status);
                                                            // if A's align < B's align, taint as source
                                                            match align_status {
                                                                Comparison::Less => {
                                                                    if !is_visible && self.rcx.type_check_option() {
                                                                        // Only if type_check_option is enabled
                                                                        // and if function is private, 
                                                                        // then we should also check callers
                                                                        let mut is_caller_checked = false;
                                                                        if let Some(fdata) = &cur_fdata {
                                                                            for f_defid in &fdata.callers {
                                                                                // progress_info!("Find caller {:?}", f_defid);
                                                                                let caller_typecheck = &call_graph.functions[&f_defid].type_check;
                                                                                // progress_info!("Caller has type check: {:?}", caller_typecheck);
                                                                                if caller_typecheck.contains("align_of") {
                                                                                    is_caller_checked |= true;
                                                                                } else {
                                                                                    is_caller_checked |= false;
                                                                                }
                                                                            }
                                                                            for constructor_defid in constructor_list {
                                                                                let constructor_typecheck = &call_graph.functions[&constructor_defid].type_check;
                                                                                // progress_info!("Constructor has type check: {:?}", constructor_typecheck);
                                                                                if constructor_typecheck.contains("align_of") {
                                                                                    is_caller_checked |= true;
                                                                                } else {
                                                                                    is_caller_checked |= false;
                                                                                }
                                                                            }
                                                                        }
                                                                        // is true
                                                                        // if either caller or pre- type check is true
                                                                        type_checked |= is_caller_checked;
                                                                    }
                                                                    // progress_info!("type check: {:?}", type_checked);
                                                                    // if pre-condition check exists, this ty conv is not bad
                                                                    if type_checked == false {
                                                                        let id2 = lplace.local.index();
                                                                        // progress_info!("warn::align from id{} to lplace{}", id, id2);
                                                                        taint_analyzer.mark_source(id2, &BehaviorFlag::CAST);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);    
                                                                    }
                                                                    
                                                                },
                                                                _ => {  },
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

                                                    if let Some(ty_def_id) = utils::extract_ty_def_id(from_ty) {
                                                        // use def_id to get symbol name of ty
                                                        let symbol_vec = ext.get_def_path(ty_def_id);
                                                        for s in symbol_vec {
                                                            if s.as_str().contains("libc") {
                                                                // the data passed from libc is already aligned
                                                                continue 'st_iter;
                                                            }
                                                        }
                                                    }

                                                    // check the potential type constructor
                                                    if !is_visible && self.rcx.type_check_option() {
                                                        let pointee_from_ty = get_pointee(from_ty);
                                                        for constructor_id in call_graph.retmap.get_func_by_ret_ty(pointee_from_ty) {
                                                            if let Some(source_list) = 
                                                                call_graph.functions[&constructor_id]
                                                                .type_conversions
                                                                .get_constructor_source(pointee_from_ty) {
                                                                    if source_list.len() != 0 {
                                                                        continue 'st_iter;
                                                                    }
                                                                }
                                                        }
                                                    }

                                                    // progress_info!("transmute::ptr-ptr");
                                                    let lc = LayoutChecker::new(self.rcx, self.param_env, from_ty, *to_ty);
                                                    let is_to_ref = is_ref(*to_ty);
                                                    let align_status = lc.get_align_status();

                                                    let (is_from_dyn, is_to_dyn) = lc.is_from_to_dyn();
                                                    if is_from_dyn | is_to_dyn {
                                                        continue;
                                                    }

                                                    let pl = get_place_from_op(&op);
                                                    match pl {
                                                        Ok(place) => {
                                                            let id = place.local.index();

                                                            // if A's align < B's align, taint as source
                                                            match align_status {
                                                                Comparison::Less | Comparison::NoideaL => {
                                                                    if !is_visible && self.rcx.type_check_option() {
                                                                        // if function is private, then we should also check callers
                                                                        let mut is_caller_checked = false;
                                                                        if let Some(fdata) = &cur_fdata {
                                                                            for f_defid in &fdata.callers {
                                                                                // progress_info!("Find caller {:?}", f_defid);
                                                                                let caller_typecheck = &call_graph.functions[&f_defid].type_check;
                                                                                // progress_info!("Caller has type check: {:?}", caller_typecheck);
                                                                                if caller_typecheck.contains("align_of") {
                                                                                    is_caller_checked |= true;
                                                                                } else {
                                                                                    is_caller_checked |= false;
                                                                                }
                                                                            }
                                                                        }
                                                                        type_checked |= is_caller_checked;
                                                                    }
                                                                    // progress_info!("type_checked / optional_type_checked: {:?}/{:?}", type_checked, optional_type_checked);
                                                                    if !type_checked && !optional_type_checked {
                                                                        // progress_info!("warn::align");
                                                                        let id2 = lplace.local.index();
                                                                        if is_to_ref {
                                                                            // misaligned reference should not exist
                                                                            taint_analyzer.mark_at_once(id2, &BehaviorFlag::TRANSMUTE);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);

                                                                            self.status
                                                                                .plain_deref
                                                                                .push(statement.source_info.span);
                                                                        } else {
                                                                            taint_analyzer.mark_source(id2, &BehaviorFlag::TRANSMUTE);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
                                                                        }
                                                                    }
                                                                    
                                                                },
                                                                _ => {},
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
                                Rvalue::Use(op)
                                | Rvalue::Repeat(op, _)
                                | Rvalue::ShallowInitBox(op, _) => {
                                    match op {
                                        Operand::Copy(pl) | Operand::Move(pl) => {
                                            if post_type_checked {
                                                // continue 'st_iter;
                                            }
                                            let id = pl.local.index();
                                            // progress_info!("[dbg] lplace: {}, rplace: {}", lplace.local.index(), pl.local.index());
                                            if pl.is_indirect() {
                                                // contains deref projection
                                                // progress_info!("warn::deref on place:{}", id);
                                                taint_analyzer.mark_sink(id);
                                                self.status
                                                    .plain_deref
                                                    .push(statement.source_info.span);
                                            }
                                        },
                                        _ => {},
                                    }
                                },
                                Rvalue::Ref(_, _, pl)
                                | Rvalue::AddressOf(_, pl)
                                | Rvalue::Len(pl)
                                | Rvalue::Discriminant(pl)
                                | Rvalue::CopyForDeref(pl) => {
                                    if post_type_checked {
                                        continue 'st_iter;
                                    }
                                    let id = pl.local.index();
                                    if pl.is_indirect() {
                                        // contains deref projection
                                        // progress_info!("warn::deref on place:{}", id);
                                        taint_analyzer.mark_sink(id);
                                        self.status
                                            .plain_deref
                                            .push(statement.source_info.span);
                                    }
                                },
                                _ => {},
                            }
                        },
                        _ => {},
                    }
                }

                // only one terminator for each basic block
                match bb.terminator.kind {
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
                        let sym = symbol_vec[ symbol_vec.len() - 1 ].as_str();

                        let mut fullsym = symbol_vec
                            .iter()
                            .map(|symbol| symbol.as_str())
                            .collect::<Vec<_>>()
                            .join("::");

                        // progress_info!("broken - find function call: {:?}", fullsym);

                        let id = dest.local.index();

                        if sym.contains("unaligned") {
                            // post condition check
                            for arg in args {
                                match arg {
                                    Operand::Copy(pl) | Operand::Move(pl) => {
                                        let id = pl.local.index();
                                        taint_analyzer
                                            .clear_source(id);
                                    },
                                    _ => {},
                                }
                            }
                        } else if sym.contains("align_of") || fullsym.contains("Layout") || sym.contains("alloc")  {
                            // pre-condition check
                            // to make sure whether this is "pre"-condition check
                            // we will see whether there is any bad type conversion marked yet
                            type_checked = true;
                        } else if sym.contains("add") {
                            // post_type_checked = true;
                        } else if sym.contains("size_of") {
                            optional_type_checked = true;
                        } else if paths::STRONG_LIFETIME_BYPASS_LIST.contains(&symbol_vec) {
                            // progress_info!("triggered with lifetime bypass: {:?}", symbol_vec);
                            for arg in args {
                                // arg: mir::Operand
                                match arg {
                                    Operand::Copy(pl) | Operand::Move(pl) => {
                                        let id = pl.local.index();
                                        taint_analyzer.mark_sink(id);
                                        self.status
                                            .strong_bypasses
                                            .push(bb.terminator.original.source_info.span);
                                    },
                                    _ => {},
                                }
                            }
                        } else if paths::WEAK_LIFETIME_BYPASS_LIST.contains(&symbol_vec) {
                            // progress_info!("triggered with lifetime bypass: {:?}", symbol_vec);
                            for arg in args {
                                match arg {
                                    Operand::Copy(pl) | Operand::Move(pl) => {
                                        let id = pl.local.index();
                                        taint_analyzer.mark_sink(id);
                                        self.status
                                            .weak_bypasses
                                            .push(bb.terminator.original.source_info.span);
                                    },
                                    _ => {},
                                }
                            }
                        } else if call_graph.functions.contains_key(&callee_did) && self.rcx.type_check_option() {
                            // inter-procedural analysis
                            // In the callee function used to dereference the raw pointer
                            // whether it contains the function to load unaligned pointer e.g., `load_unaligned`
                            // progress_info!("Find callee: {:?} information in the call graph", sym);

                            let incl_type_check = &call_graph.functions[&callee_did].type_check;

                            if incl_type_check.contains("unaligned") {
                                // progress_info!("Find unaligned deref in callee: {:?}/{:?}", callee_did, sym);

                                for arg in args {
                                    match arg {
                                        Operand::Copy(pl) | Operand::Move(pl) => {
                                            let id = pl.local.index();
                                            taint_analyzer
                                                .clear_source(id);
                                        },
                                        _ => {},
                                    }
                                }
                            }
                        }
                    },
                    ir::TerminatorKind::Return => {
                        // _0 is always considered as return value
                        let return_pl0 = self.body.local_decls().get(RETURN_PLACE);
                        if return_pl0.is_some() {
                            match return_pl0.unwrap().ty.kind() {
                                TyKind::Ref(..) => {
                                    taint_analyzer.mark_sink(0);
                                    self.status
                                        .plain_deref
                                        .push(bb.terminator.original.source_info.span);
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

fn is_ref<'tcx>(ptr_ty: Ty<'tcx>) -> bool {
    if let ty::Ref(..) = ptr_ty.kind() {
        true
    } else {
        false
    }
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
// Used to associate each broken layout bug report with its cause.
bitflags! {
    #[derive(Default)]
    pub struct BehaviorFlag: u16 {
        const CAST = 0b00000001;
        const TRANSMUTE = 0b00000010;
    }
}

impl IntoReportLevel for BehaviorFlag {
    fn report_level(&self, checked: bool) -> ReportLevel {
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
        
        if checked == false {
            ReportLevel::Warning
        } else {
            ReportLevel::Error
        }
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
