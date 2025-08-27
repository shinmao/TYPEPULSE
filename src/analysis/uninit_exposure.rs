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
    analysis::{AnalysisKind, IntoReportLevel, LayoutChecker, Comparison, SatisfiedChecker, SatisfiedPair},
    graph::TaintAnalyzer,
    ir,
    paths::{self, *},
    report::{Report, ReportLevel},
    utils,
    visitor::ContainsUnsafe,
    context::TypePulseCtxt,
    progress_info,
    progress_warn,
};
use crate::call_graph::CallGraph;

#[derive(Debug, Snafu)]
pub enum UninitExposureError {
    PushPopBlock { backtrace: Backtrace },
    ResolveError { backtrace: Backtrace },
    InvalidSpan { backtrace: Backtrace },
}

impl AnalysisError for UninitExposureError {
    fn kind(&self) -> AnalysisErrorKind {
        use UninitExposureError::*;
        match self {
            PushPopBlock { .. } => AnalysisErrorKind::Unreachable,
            ResolveError { .. } => AnalysisErrorKind::OutOfScope,
            InvalidSpan { .. } => AnalysisErrorKind::Unreachable,
        }
    }
}

pub struct UninitExposureChecker<'tcx> {
    rcx: TypePulseCtxt<'tcx>,
}

impl<'tcx> UninitExposureChecker<'tcx> {
    pub fn new(rcx: TypePulseCtxt<'tcx>) -> Self {
        UninitExposureChecker { rcx }
    }

    pub fn analyze(self) {
        let tcx = self.rcx.tcx();
        let hir_map = tcx.hir();

        // Fist time to iterates all (type, related function) pairs to construct a completed call graph
        for (_ty_hir_id, (body_id, related_item_span)) in self.rcx.types_with_related_items() {

            let body_did = hir_map.body_owner_def_id(body_id).to_def_id();
            
            //progress_info!("Phase 1: Call Graph - InconsistentLayoutChecker::analyze({})", 
            //         tcx.def_path_str(body_did)
            //);

            self.rcx.translate_body(body_did);
        }

        // Iterates all (type, related function) pairs
        for (_ty_hir_id, (body_id, related_item_span)) in self.rcx.types_with_related_items() {
            // print the funciton name of current body
            // progress_info!("Phase 2: Detection - InconsistentLayoutChecker::analyze({})", 
            //             tcx.def_path_str(hir_map.body_owner_def_id(body_id).to_def_id())
            // );

            let body_did = hir_map.body_owner_def_id(body_id).to_def_id();

            // based on function itself
            let f_visible = utils::check_visibility(tcx, body_did);

            // progress_info!("{:?}", f_visible);

            // if function is public, then we still need to check whether it is method and self
            // if function is private, we just need to pass private
            // visible && ty_visible
            let ty_visible = if utils::has_self_parameter(tcx, body_did) {
                if let Some(self_ty) = utils::get_method_self_ty(tcx, body_did) {
                    utils::check_ty_visibility(tcx, self_ty)
                } else {
                    false
                }
            } else {
                f_visible
            };

            let visible = f_visible && ty_visible;

            // progress_info!("The function is visible: {:?}", visible);


            if let Some(status) = inner::UninitExposureBodyAnalyzer::analyze_body(self.rcx, body_id, visible)
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

                    for &span in status.plain_deref_spans() {
                        color_span.add_sub_span(Color::Blue, span);
                    }
                    
                    for &span in status.ty_conv_spans() {
                        color_span.add_sub_span(Color::Green, span);
                    }

                    for &span in status.access_uninit_spans() {
                        color_span.add_sub_span(Color::Cyan, span);
                    }

                    typepulse_report(Report::with_color_span(
                        tcx,
                        behavior_flag.report_level(visible),
                        AnalysisKind::UninitExposure(behavior_flag),
                        format!(
                            "Potential uninit exposure issue in `{}`",
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
    pub struct UninitExposureStatus {
        strong_bypasses: Vec<Span>,
        weak_bypasses: Vec<Span>,
        plain_deref: Vec<Span>,
        unresolvable_generic_functions: Vec<Span>,
        ty_convs: Vec<Span>,
        access_uninit: Vec<Span>,
        behavior_flag: BehaviorFlag,
    }

    impl UninitExposureStatus {
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

        pub fn access_uninit_spans(&self) -> &Vec<Span> {
            &self.access_uninit
        }
    }

    pub struct UninitExposureBodyAnalyzer<'a, 'tcx> {
        rcx: TypePulseCtxt<'tcx>,
        body: &'a ir::Body<'tcx>,
        param_env: ParamEnv<'tcx>,
        status: UninitExposureStatus,
    }

    impl<'a, 'tcx> UninitExposureBodyAnalyzer<'a, 'tcx> {
        fn new(rcx: TypePulseCtxt<'tcx>, param_env: ParamEnv<'tcx>, body: &'a ir::Body<'tcx>) -> Self {
            UninitExposureBodyAnalyzer {
                rcx,
                body,
                param_env,
                status: Default::default(),
            }
        }

        pub fn analyze_body(rcx: TypePulseCtxt<'tcx>, body_id: BodyId, visible: bool) -> Option<UninitExposureStatus> {
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
                //progress_info!("special case required");
                // Special case for paths discovery
                trace_calls_in_body(rcx, body_did);
                None
            } else if ContainsUnsafe::contains_unsafe(rcx.tcx(), body_id) {
                let fn_sig = rcx.tcx().fn_sig(body_did).skip_binder();
                if let Unsafety::Unsafe = fn_sig.unsafety() {
                    //progress_info!("The function is unsafe");
                    None
                } else {
                    //progress_info!("This function contains unsafe block");
                    let (rc_body, rc_call_graph) = rcx.translate_body(body_did);
                    match rc_body.as_ref() {
                        Err(e) => {
                            // MIR is not available for def - log it and continue
                            e.log();
                            None
                        }
                        Ok(body) => {
                            let param_env = rcx.tcx().param_env(body_did);
                            let body_analyzer = UninitExposureBodyAnalyzer::new(rcx, param_env, body);
                            Some(body_analyzer.analyze(rc_call_graph.as_ref(), body_did, visible))
                        }
                    }
                }
            } else {
                // We don't perform interprocedural analysis,
                // thus safe functions are considered safe
                Some(Default::default())
            }
        }

        fn analyze(mut self, call_graph: &CallGraph<'tcx>, cur_func_id: DefId, visible: bool) -> UninitExposureStatus {
            // progress_info!("Curr function has id: {:?}", cur_func_id);
            let mut taint_analyzer = TaintAnalyzer::new(self.body);

            // This flag is control-flow sensitive and used in single function
            // will be checked before type conversion
            // ie. pre-condition check
            let mut type_checked = false;

            let tcx = self.rcx.tcx();

            // TyCtxt
            let ext = tcx.ext();

            let cur_fdata = if call_graph.functions.contains_key(&cur_func_id) {
                // progress_info!("Phase 2 - Find curr function in call graph");
                Some(&call_graph.functions[&cur_func_id])
            } else {
                // progress_info!("Phase 2 - Not find curr function in call graph");
                None
            };

            if let Some(fdata) = cur_fdata {
                for f_def_id in &fdata.callers {
                    // progress_info!("Find caller: {:?}", f_def_id);
                }
            }

            for bb in self.body.basic_blocks() {
                // statement here is mir::Statement without translation
                // while iterating statements, we plan to mark ty conv as source / plain deref as sink
                'st_iter: for statement in &bb.statements {
                    match &statement.kind {
                        StatementKind::Assign(box (lplace, rval)) => {
                            // lhs could also contains deref operation
                            if lplace.is_indirect() {
                                // contains deref projection
                                // progress_info!("warn::deref on place:{}", lplace.local.index());
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
                                            //progress_info!("cast::ptr-ptr");
                                            let casted_id = match op {
                                                Operand::Copy(rplace) | Operand::Move(rplace) => {
                                                    let id = rplace.local.index();
                                                    Some(id)
                                                },
                                                _ => None,
                                            };

                                            let f_ty = get_ty_from_op(self.body, self.rcx, &op);
                                            match f_ty {
                                                Ok(from_ty) => {
                                                    // if let Some(ty_def_id) = utils::extract_ty_def_id(from_ty) {
                                                    //     // use def_id to get symbol name of ty
                                                    //     let symbol_vec = ext.get_def_path(ty_def_id);
                                                    //     for s in symbol_vec {
                                                    //         if s.as_str().contains("libc") {
                                                    //             // the data passed from libc is already stable
                                                    //             continue 'st_iter;
                                                    //         }
                                                    //     }
                                                    // }


                                                    let lc = LayoutChecker::new(self.rcx, self.param_env, from_ty, *to_ty);
                                                    let fty = lc.get_from_ty();
                                                    let tty = lc.get_to_ty();
                                                    let align_status = lc.get_align_status();
                                                    let size_status = lc.get_size_status();
                                                    let ty_bnd = lc.get_ty_bnd();

                                                    // used when ty_bnd != 0
                                                    let sc = SatisfiedChecker::new(&lc);

                                                    // progress_info!("tty kind: {:?}", tty.kind());

                                                    if fty.to_string().contains("TypeId") || tty.to_string().contains("TypeId") {
                                                        continue 'st_iter;
                                                    }

                                                    // if let Some(fdata) = cur_fdata {
                                                    //     if let Some(source_list) = fdata.type_conversions.get_constructor_source(fty) {
                                                    //         if source_list.len() != 0 {
                                                    //             progress_info!("Find previous type conversion");
                                                    //             continue 'st_iter;
                                                    //         }
                                                    //     }
                                                    // }
                                                    
    
                                                    let pl = get_place_from_op(&op);
                                                    match pl {
                                                        Ok(place) => {
                                                            let id = place.local.index();
    
                                                            // check
                                                            // (gen > prim) (adt > prim)
                                                            // (gen > adt) (adt > adt)
                                                            let (is_from_prime, is_to_prime) = lc.is_from_to_primitive();
                                                            let (is_from_adt, is_to_adt) = lc.is_from_to_adt();
                                                            let (is_from_gen, is_to_gen) = lc.is_from_to_generic();
                                                            let (is_from_arr_slice, is_to_arr_slice) = lc.is_from_to_arr_slice();
                                                            let (is_from_foreign, is_to_foreign) = lc.is_from_to_foreign();
                                                            let (is_from_trans, is_to_trans) = lc.is_from_to_transparent();
                                                            let (is_from_c, is_to_c) = lc.is_from_to_c();
                                                            let (is_from_dyn, is_to_dyn) = lc.is_from_to_dyn();
                                                            let (is_from_tuple, is_to_tuple) = lc.is_from_to_zero_tuple();

                                                            if is_from_gen == true && is_to_gen == false && tty.to_string() != "usize" && !tty.is_c_void(tcx) && !tty.contains(fty) {
                                                                // generic > concrete
                                                                // call TraitChecker for help
                                                                if (ty_bnd.len() == 0) && visible  {
                                                                    // it could be arbitrary type
                                                                    if is_to_prime | is_to_arr_slice {
                                                                        // progress_info!("warn::cast (gen>prime/arr/slice) from id{} to lplace{}", id, lplace.local.index());
                                                                        taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);
                                                                    } else if is_to_adt {
                                                                        // adt is required to have stable layout
                                                                        if !is_to_trans && !is_to_c {
                                                                            // progress_info!("warn::cast (gen>adt) from id{} to lplace{}", id, lplace.local.index());
                                                                            taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
                                                                        }
                                                                    }
                                                                } else if visible {
                                                                    match sc.get_consistent_status() {
                                                                        SatisfiedPair::Adt2Prime |
                                                                        SatisfiedPair::Adt2ArrSlice => {
                                                                            taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
                                                                        },
                                                                        SatisfiedPair::Adt2Adt => {
                                                                            if !is_to_trans && !is_to_c {
                                                                                taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                                self.status
                                                                                    .ty_convs
                                                                                    .push(statement.source_info.span);
                                                                            }
                                                                        },
                                                                        _ => {},
                                                                    }
                                                                }
                                                            } else if is_from_gen == false && is_to_gen == true && !fty.contains(tty) {
                                                                // concrete > generic
                                                                if (ty_bnd.len() == 0) && (type_checked == false) {
                                                                    // it could be arbitrary types
                                                                    if is_from_adt {
                                                                        // progress_info!("warn::cast (adt>gen) from id{} to lplace{}", id, lplace.local.index());
                                                                        let mut controllable = false;
                                                                        for (loc, dec) in self.body.local_decls().iter_enumerated() {
                                                                            if self.body.local_kind(loc) == 1 {
                                                                                let arg_idx = loc.index();
                                                                                // progress_info!("dec: {:?}", dec);
                                                                                if let Some(id) = casted_id {
                                                                                    if taint_analyzer.is_reachable(arg_idx, id) {
                                                                                        // fty can be controlled by attacker
                                                                                        controllable |= true;
                                                                                        break;
                                                                                    }
                                                                                }
                                                                            }
                                                                            
                                                                        }
                                                                        // progress_info!("controlled by attacker: {:?}", controllable);
                                                                        if fty.is_c_void(tcx) {
                                                                            if !visible {
                                                                                continue 'st_iter;
                                                                            } else if !controllable {
                                                                                continue 'st_iter;
                                                                            }
                                                                        } 
                                                                        taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);
                                                                    }
                                                                } else if visible {
                                                                    match sc.get_consistent_status() {
                                                                        SatisfiedPair::Adt2Prime |
                                                                        SatisfiedPair::Adt2ArrSlice => {
                                                                            taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
                                                                        },
                                                                        SatisfiedPair::Adt2Adt => {
                                                                            if !is_to_trans && !is_to_c {
                                                                                taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                                self.status
                                                                                    .ty_convs
                                                                                    .push(statement.source_info.span);
                                                                            }
                                                                        },
                                                                        _ => {},
                                                                    }
                                                                }
                                                            } else if is_from_adt && is_to_adt && !fty.is_c_void(tcx) &&
                                                                        (type_checked == false) {
                                                                // if one of the adt doesn't have stable layout, then it is dangerous
                                                                // if ((!is_from_c && !is_to_c) && (!is_from_trans && !is_to_trans)) && (fty.to_string() != tty.to_string()) {
                                                                // progress_info!("(adt>adt) is_from_c:{:?}, is_from_trans:{:?}", is_from_c, is_from_trans);
                                                                if (!is_from_c && !is_from_trans && !is_to_trans) && (fty.to_string() != tty.to_string()) {
                                                                    // progress_info!("warn::cast (adt>adt) from id{} to lplace{}", id, lplace.local.index());
                                                                    // progress_warn!("Casting type with unstable layout, please take care before using it!");
                                                                    taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                    self.status
                                                                        .ty_convs
                                                                        .push(statement.source_info.span);
                                                                }
                                                            } else if (is_from_adt && is_to_prime && tty.to_string() != "usize") | (is_from_adt && is_to_arr_slice) {
                                                                if let Some(ty_def_id) = utils::extract_ty_def_id(fty) {
                                                                    // use def_id to get symbol name of ty
                                                                    let symbol_vec = ext.get_def_path(ty_def_id);
                                                                    let len = symbol_vec.len();
                                                                    if symbol_vec[len - 1].as_str().contains("Vec") && !visible {
                                                                        continue 'st_iter;
                                                                    }
                                                                }
                                                                let mut controllable = false;
                                                                for (loc, dec) in self.body.local_decls().iter_enumerated() {
                                                                    if self.body.local_kind(loc) == 1 {
                                                                        let arg_idx = loc.index();
                                                                        // progress_info!("dec: {:?}", dec);
                                                                        if let Some(id) = casted_id {
                                                                            if taint_analyzer.is_reachable(arg_idx, id) {
                                                                                // fty can be controlled by attacker
                                                                                controllable |= true;
                                                                                break;
                                                                            }
                                                                        }
                                                                    }
                                                                    
                                                                }
                                                                // progress_info!("controlled by attacker: {:?}", controllable);
                                                                if fty.is_c_void(tcx) {
                                                                    if !visible {
                                                                        continue 'st_iter;
                                                                    } else if !controllable {
                                                                        continue 'st_iter;
                                                                    }
                                                                } 
                                                                if !is_from_trans && !is_from_c  && (type_checked == false) {
                                                                    progress_info!("Inconsistent Layout Bug: Waiting type to be deref as invalid type...");
                                                                    taint_analyzer.mark_source(id, &BehaviorFlag::CAST);
                                                                    self.status
                                                                        .ty_convs
                                                                        .push(statement.source_info.span);
                                                                }
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

                                                    // if let Some(ty_def_id) = utils::extract_ty_def_id(from_ty) {
                                                    //     // use def_id to get symbol name of ty
                                                    //     let symbol_vec = ext.get_def_path(ty_def_id);
                                                    //     for s in symbol_vec {
                                                    //         if s.as_str().contains("libc") {
                                                    //             // the data passed from libc is already stable
                                                    //             continue 'st_iter;
                                                    //         }
                                                    //     }
                                                    // }

                                                    //progress_info!("transmute::ptr-ptr");
                                                    let lc = LayoutChecker::new(self.rcx, self.param_env, from_ty, *to_ty);
                                                    let fty = lc.get_from_ty();
                                                    let tty = lc.get_to_ty();
                                                    let align_status = lc.get_align_status();
                                                    let size_status = lc.get_size_status();
                                                    let ty_bnd = lc.get_ty_bnd();

                                                    // used when ty_bnd != 0
                                                    let sc = SatisfiedChecker::new(&lc);

                                                    if fty.to_string().contains("TypeId") || tty.to_string().contains("TypeId") {
                                                        continue 'st_iter;
                                                    }
    
                                                    let pl = get_place_from_op(&op);
                                                    match pl {
                                                        Ok(place) => {
                                                            let id = place.local.index();
    
                                                            // check
                                                            // (gen > prim) (adt > prim)
                                                            // (gen > adt) (adt > adt)
                                                            let (is_from_prime, is_to_prime) = lc.is_from_to_primitive();
                                                            let (is_from_adt, is_to_adt) = lc.is_from_to_adt();
                                                            let (is_from_gen, is_to_gen) = lc.is_from_to_generic();
                                                            let (is_from_arr_slice, is_to_arr_slice) = lc.is_from_to_arr_slice();
                                                            let (is_from_foreign, is_to_foreign) = lc.is_from_to_foreign();
                                                            let (is_from_trans, is_to_trans) = lc.is_from_to_transparent();
                                                            let (is_from_c, is_to_c) = lc.is_from_to_c();
                                                            let (is_from_dyn, is_to_dyn) = lc.is_from_to_dyn();
                                                            // progress_info!("from_prime: {}, from_adt: {}, from_gen: {}, from_foreign: {}, from_transparent: {}, from_c: {}, from_dyn: {}", is_from_prime, is_from_adt, is_from_gen, is_from_foreign, is_from_trans, is_from_c, is_from_dyn);
                                                            // progress_info!("to_prime: {}, to_adt: {}, to_gen: {}, to_foreign: {}, to_transparent: {}, to_c: {}, to_dyn: {}", is_to_prime, is_to_adt, is_to_gen, is_to_foreign, is_to_trans, is_to_c, is_to_dyn);
                                                            if is_from_gen == true && is_to_gen == false && tty.to_string() != "usize" && !tty.is_c_void(tcx) && !tty.contains(fty) {
                                                                // generic > concrete
                                                                // call TraitChecker for help
                                                                if (ty_bnd.len() == 0) && visible && !type_checked {
                                                                    // it could be arbitrary type
                                                                    if is_to_prime | is_to_arr_slice {
                                                                        // progress_info!("warn::transmute (gen>prime/arr/slice) from id{} to lplace{}", id, lplace.local.index());
                                                                        taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);
                                                                    } else if is_to_adt {
                                                                        // adt is required to have stable layout
                                                                        if !is_to_trans && !is_to_c {
                                                                            // progress_info!("warn::transmute (gen>adt) from id{} to lplace{}", id, lplace.local.index());
                                                                            taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
                                                                        }
                                                                    }
                                                                } else {
                                                                    match sc.get_consistent_status() {
                                                                        SatisfiedPair::Adt2Prime |
                                                                        SatisfiedPair::Adt2ArrSlice => {
                                                                            taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
                                                                        },
                                                                        SatisfiedPair::Adt2Adt => {
                                                                            if !is_to_trans && !is_to_c {
                                                                                taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                                self.status
                                                                                    .ty_convs
                                                                                    .push(statement.source_info.span);
                                                                            }
                                                                        },
                                                                        _ => {},
                                                                    }
                                                                }
                                                            } else if is_from_gen == false && is_to_gen == true && !fty.contains(tty) {
                                                                // concrete > generic
                                                                if (ty_bnd.len() == 0) && (type_checked == false) {
                                                                    // it could be arbitrary types
                                                                    let from_ty_name = fty.to_string();
                                                                    if is_from_adt && (!from_ty_name.contains("MaybeUninit")) {
                                                                        // progress_info!("warn::transmute (adt>gen) from id{} to lplace{}", id, lplace.local.index());
                                                                        taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                        self.status
                                                                            .ty_convs
                                                                            .push(statement.source_info.span);
                                                                    }
                                                                } else {
                                                                    match sc.get_consistent_status() {
                                                                        SatisfiedPair::Adt2Prime |
                                                                        SatisfiedPair::Adt2ArrSlice => {
                                                                            taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                            self.status
                                                                                .ty_convs
                                                                                .push(statement.source_info.span);
                                                                        },
                                                                        SatisfiedPair::Adt2Adt => {
                                                                            if !is_to_trans && !is_to_c {
                                                                                taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                                self.status
                                                                                    .ty_convs
                                                                                    .push(statement.source_info.span);
                                                                            }
                                                                        },
                                                                        _ => {},
                                                                    }
                                                                }
                                                            } else if is_from_adt && is_to_adt && !fty.is_c_void(tcx) &&
                                                                    (type_checked == false) {
                                                                // if one of the adt doesn't have stable layout, then it is dangerous
                                                                let from_ty_name = fty.to_string();
                                                                // if ((!is_from_c && !is_to_c) && (!is_from_trans && !is_to_trans)) && (from_ty_name != tty.to_string()) && (!from_ty_name.contains("MaybeUninit")) {
                                                                if (!is_from_c && !is_from_trans && !is_to_trans) && (fty.to_string() != tty.to_string()) {
                                                                    //progress_info!("warn::transmute (adt>adt) from id{} to lplace{}", id, lplace.local.index());
                                                                    taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                    self.status
                                                                        .ty_convs
                                                                        .push(statement.source_info.span);
                                                                }
                                                            } else if (is_from_adt && is_to_prime && tty.to_string() != "usize") | (is_from_adt && is_to_arr_slice) {
                                                                let from_ty_name = fty.to_string();
                                                                // simd is stable repr()
                                                                let from_ty_simd = fty.is_simd();
                                                                progress_info!("hi, is from transparent wrapper?: {:?}", is_from_trans);
                                                                if !is_from_trans && !is_from_c && !fty.is_c_void(tcx) && (type_checked == false) && !from_ty_simd {
                                                                    // progress_info!("warn::transmute (adt>prime/arr/slice) from id{} to lplace{}", id, lplace.local.index());
                                                                    taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                    self.status
                                                                        .ty_convs
                                                                        .push(statement.source_info.span);
                                                                }
                                                            } else if is_from_dyn && is_to_adt && !tty.is_c_void(tcx) && (type_checked == false) {
                                                                // this case could only happen in
                                                                // tranmsute
                                                                // ptr to trait obj is fat ptr
                                                                // fat ptr>thin is not allowed in cast
                                                                // progress_info!("warn::transmute (trait obj>struct) from id{} to lplace{}", id, lplace.local.index());
                                                                taint_analyzer.mark_source(id, &BehaviorFlag::TRANSMUTE);
                                                                self.status
                                                                    .ty_convs
                                                                    .push(statement.source_info.span);
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

                        let callee_sig = self.rcx.tcx().fn_sig(callee_did).skip_binder();
                        let is_callee_unsafe = if let Unsafety::Unsafe = callee_sig.unsafety() {
                            true
                        } else {
                            false
                        };

                        if sym.contains("write_unaligned") {
                            // core::ptr::write_unaligned is used to init uninitialized memory
                            let id = dest.local.index();
                            taint_analyzer
                                .clear_source(id);
                        } else if sym.contains("read_unaligned") ||
                                sym.contains("from_raw_parts") {
                            // progress_info!("triggered with lifetime bypass: {:?}", symbol_vec);
                            if is_callee_unsafe {
                                for arg in args {
                                    match arg {
                                        Operand::Copy(pl) | Operand::Move(pl) => {
                                            let id = pl.local.index();
                                            taint_analyzer.mark_sink(id);
                                            self.status
                                                .access_uninit
                                                .push(bb.terminator.original.source_info.span);
                                        },
                                        _ => {},
                                    }
                                }
                            }
                        } else if sym.contains("assume_init") || 
                                    sym.contains("size_of") ||
                                    fullsym.contains("TypeId") {
                            // developers can guarantee the memory is initialized
                            if self.rcx.type_check_option() {
                                type_checked = true;
                            }
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
                                // arg: mir::Operand
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
                            // if the callee include a pre type check
                            // e.g., typeid

                            let incl_type_check = &call_graph.functions[&callee_did].type_check;

                            // pre type check
                            if incl_type_check.contains("typeid") {
                                type_checked = true;
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
// Used to associate each uninit exposure bug report with its cause.
bitflags! {
    #[derive(Default)]
    pub struct BehaviorFlag: u16 {
        const CAST = 0b00000001;
        const TRANSMUTE = 0b00000010;
    }
}

impl IntoReportLevel for BehaviorFlag {
    fn report_level(&self, visibility: bool) -> ReportLevel {
        use BehaviorFlag as Flag;

        let high = Flag::CAST | Flag::TRANSMUTE;

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
