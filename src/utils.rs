use rustc_middle::ty::{Ty, 
    Instance, 
    InstanceDef, 
    TyCtxt, 
    TyKind, 
    InternalSubsts,  
    subst::SubstsRef,
    Visibility,
    Clause,
    ParamEnv,
    PredicateKind,
    OutlivesPredicate,
};
use rustc_middle::mir::pretty::write_mir_pretty;
use rustc_span::{CharPos, Span, def_id::DefId, def_id::LocalDefId};
use rustc_hir::def::Res;

use std::io::Write;
use std::rc::Rc;

use termcolor::{Buffer, Color, ColorSpec, WriteColor};

use crate::compile_time_sysroot;
use crate::analysis::get_pointee;
use crate::progress_info;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
struct ColorEventId(usize);

struct ColorStack(Vec<(Color, ColorEventId)>);

impl ColorStack {
    pub fn new() -> Self {
        ColorStack(Vec::new())
    }

    pub fn handle_event(&mut self, event: &ColorEvent) {
        match event.color {
            Some(color) => self.0.push((color, event.id)),
            None => {
                for i in (0..self.0.len()).rev() {
                    if self.0[i].1 == event.id {
                        self.0.remove(i);
                        return;
                    }
                }
            }
        };
    }

    pub fn current_spec(&self) -> ColorSpec {
        let mut spec = ColorSpec::new();

        match self.0.last() {
            Some((color, _)) => spec.set_fg(Some(*color)),
            None => spec.set_reset(true),
        };

        spec
    }
}

#[derive(Clone)]
struct ColorEvent {
    // Some(color) for start, None for clear
    color: Option<Color>,
    line: usize,
    col: CharPos,
    id: ColorEventId,
}

impl PartialEq for ColorEvent {
    fn eq(&self, other: &Self) -> bool {
        self.line == other.line
            && self.col == other.col
            && self.color.is_some() == other.color.is_some()
    }
}

impl Eq for ColorEvent {}

impl PartialOrd for ColorEvent {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ColorEvent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.line != other.line {
            return self.line.cmp(&other.line);
        }

        if self.col != other.col {
            return self.col.cmp(&other.col);
        }

        if self.color.is_some() != other.color.is_some() {
            return self.color.is_some().cmp(&other.color.is_some());
        }

        std::cmp::Ordering::Equal
    }
}


pub struct ColorSpan<'tcx> {
    tcx: TyCtxt<'tcx>,
    main_span: Span,
    main_span_start: rustc_span::Loc,
    main_span_end: rustc_span::Loc,
    id_counter: usize,
    sub_span_events: Vec<ColorEvent>,
}

impl<'tcx> ColorSpan<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, main_span: Span) -> Option<Self> {
        let source_map = tcx.sess.source_map();
        if let Ok((main_span_start, main_span_end)) = source_map.is_valid_span(main_span) {
            // Sanity check
            if !Rc::ptr_eq(&main_span_start.file, &main_span_end.file) {
                return None;
            }

            Some(ColorSpan {
                tcx,
                main_span,
                main_span_start,
                main_span_end,
                id_counter: 0,
                sub_span_events: Vec::new(),
            })
        } else {
            None
        }
    }

    pub fn main_span(&self) -> Span {
        self.main_span
    }

    /// Returns true if span is successfully added
    pub fn add_sub_span(&mut self, color: Color, span: Span) -> bool {
        let source_map = self.tcx.sess.source_map();
        if let Ok((start_loc, end_loc)) = source_map.is_valid_span(span) {
            // Reports from macros may be in another file and we don't handle them
            if !Rc::ptr_eq(&start_loc.file, &self.main_span_start.file)
                || !Rc::ptr_eq(&start_loc.file, &self.main_span_end.file)
            {
                return false;
            }

            let event_id = ColorEventId(self.id_counter);
            self.id_counter += 1;

            self.sub_span_events.push(ColorEvent {
                color: Some(color),
                line: start_loc.line,
                col: start_loc.col,
                id: event_id,
            });
            self.sub_span_events.push(ColorEvent {
                color: None,
                line: end_loc.line,
                col: end_loc.col,
                id: event_id,
            });
            return true;
        } else {
            return false;
        }
    }

    pub fn to_colored_string(&self) -> String {
        let mut events = self.sub_span_events.clone();
        events.sort();
        let mut events_iter = events.into_iter().peekable();

        let source_map = self.tcx.sess.source_map();
        let mut buffer = Buffer::ansi();

        if let (Ok((start_loc, end_loc)), Ok(snippet)) = (
            source_map.is_valid_span(self.main_span),
            source_map.span_to_snippet(self.main_span),
        ) {
            let start_line = start_loc.line;
            let end_line = end_loc.line;

            while let Some(event) = events_iter.peek() {
                if event.line < start_line {
                    // Discard spans before the start loc
                    events_iter.next();
                } else {
                    break;
                }
            }

            let mut color_stack = ColorStack::new();
            for (line_idx, line_content) in (start_line..=end_line).zip(snippet.lines()) {
                let mut current_col = if line_idx == start_line {
                    start_loc.col
                } else {
                    CharPos(0)
                };

                let mut handle_color_event = |buffer: &mut Buffer, col: CharPos| {
                    while let Some(event) = events_iter.peek() {
                        if event.line == line_idx && event.col == col {
                            color_stack.handle_event(event);
                            events_iter.next();

                            let spec = color_stack.current_spec();
                            buffer.set_color(&spec).map_err(|e| warn!("{}", e)).ok();
                        } else {
                            break;
                        }
                    }
                };

                for ch in line_content.chars() {
                    handle_color_event(&mut buffer, current_col);
                    write!(buffer, "{}", ch).ok();
                    current_col.0 += 1;
                }

                // Handle reset
                handle_color_event(&mut buffer, current_col);
                write!(buffer, "\n").ok();
            }

            // Reset the color after printing the span just in case
            buffer
                .set_color(ColorSpec::new().set_reset(true))
                .map_err(|e| warn!("{}", e))
                .ok();

            String::from_utf8_lossy(buffer.as_slice()).into()
        } else {
            format!("Unable to get span for {:?}", self.main_span)
        }
    }
}

pub fn print_span<'tcx>(tcx: TyCtxt<'tcx>, span: &Span) {
    let source_map = tcx.sess.source_map();
    eprintln!(
        "{}\n{}\n",
        source_map.span_to_diagnostic_string(span.clone()),
        source_map.span_to_snippet(span.clone()).unwrap()
    );
}

pub fn print_span_to_file<'tcx>(tcx: TyCtxt<'tcx>, span: &Span, output_name: &str) {
    let source_map = tcx.sess.source_map();
    let sysroot = compile_time_sysroot().expect("Failed to fetch sysroot");
    let filename = format!("{}/logs/{}", sysroot, output_name);
    let content = format!(
        "{}\n{}\n",
        source_map.span_to_diagnostic_string(span.clone()),
        source_map.span_to_snippet(span.clone()).unwrap()
    );
    std::fs::write(filename, content).expect("Unable to write file");
}

pub fn print_mir<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) {
    info!("Printing MIR for {:?}", instance);

    match instance.def {
        InstanceDef::Item(_) => {
            if tcx.is_mir_available(instance.def.def_id()) {
                let stderr = std::io::stderr();
                let mut handle = stderr.lock();
                if let Err(_) = write_mir_pretty(tcx, Some(instance.def.def_id()), &mut handle) {
                    error!(
                        "Cannot print MIR: error while printing `{:?}`",
                        instance.def.def_id()
                    );
                }
            } else {
                info!("Cannot print MIR: no MIR for `{:?}`", &instance);
            }
        }
        _ => info!("Cannot print MIR: `{:?}` is a shim", instance),
    }
}

pub fn print_mir_to_file<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>, output_name: &str) {
    let sysroot = compile_time_sysroot().expect("Failed to fetch sysroot");
    let filename = format!("{}/logs/{}", sysroot, output_name);
    info!("Printing MIR for {:?} to {}", instance, filename);

    match instance.def {
        InstanceDef::Item(_) => {
            if tcx.is_mir_available(instance.def.def_id()) {
                let mut handle =
                    std::fs::File::create(filename).expect("Error while creating file");
                if let Err(_) = write_mir_pretty(tcx, Some(instance.def.def_id()), &mut handle) {
                    error!(
                        "Cannot print MIR: error while printing `{:?}`",
                        instance.def.def_id()
                    );
                }
            } else {
                info!("Cannot print MIR: no MIR for `{:?}`", &instance);
            }
        }
        _ => info!("Cannot print MIR: `{:?}` is a shim", instance),
    }
}

pub fn check_visibility<'tcx>(tcx: TyCtxt<'tcx>, func_defid: DefId) -> bool {
    // return false if function can't be reachable to users
    let visible = tcx.visibility(func_defid).is_public();
    if visible == false {
        return false;
    }

    if func_defid.is_local() {
        if let Some(local_defid) = func_defid.as_local() {
            let module_moddefid = tcx.parent_module_from_def_id(local_defid);
            let module_defid = module_moddefid.to_def_id();
            if !tcx.visibility(module_defid).is_public() {
                return is_re_exported(tcx, func_defid, module_moddefid);
            }
        }
    }
    true
}

fn is_re_exported<'tcx>(tcx: TyCtxt<'tcx>, target_defid: DefId, module_defid: LocalDefId) -> bool {
    for child in tcx.module_children_local(module_defid) {
        if child.vis.is_public() {
            if let Some(def_id) = child.res.opt_def_id() {
                if def_id == target_defid {
                    return true;
                }
            }
        }
    }

    false
}


pub fn check_ty_visibility<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(..)
        | TyKind::Uint(..)
        | TyKind::Float(..)
        | TyKind::Str
        | TyKind::Array(..)
        | TyKind::Slice(..)
        | TyKind::Tuple(..)
        | TyKind::Never => true,

        TyKind::Adt(adt_def, _) => {
            if adt_def.is_struct() {
                for field in adt_def.all_fields() {
                    if let Visibility::Restricted(_) = field.vis {
                        return false;
                    }
                }
                return true;
            }
            true
        }
        _ => true,
    }
}

pub fn find_import_alias<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<String> {
    for item_id in tcx.hir().items() {
        let item = tcx.hir().item(item_id);
        if let rustc_hir::ItemKind::Use(path, _) = &item.kind {
            // Iterate through the `SmallVec` to find a matching `Res`
            for res in &path.res {
                if let Res::Def(_, import_def_id) = res {
                    if *import_def_id == def_id {
                        return Some(item.ident.name.to_string());
                    }
                }
            }
        }
    }
    None
}

pub fn is_trait_method<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    if tcx.trait_of_item(def_id).is_some() {
        true
    } else {
        false
    }
}

/// Returns true if the function has an explicit `self` (either `self` or `&(mut) self`) as its first 
/// parameter, allowing method calls.
pub fn has_self_parameter<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    if let Some(associated_item) = tcx.opt_associated_item(def_id) {
        associated_item.fn_has_self_parameter
    } else {
        false
    }
}


pub fn get_method_self_ty<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Ty<'tcx>> {
    let fn_sig = tcx.fn_sig(def_id);
    let fn_sig = tcx.erase_late_bound_regions(fn_sig.skip_binder());

    if let Some(self_ty) = fn_sig.inputs().get(0) {
        // progress_info!("self ty: {:?}", *self_ty);
        Some(get_pointee(*self_ty))
    } else {
        None
    }
}

pub fn resolve_impl_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_method_def_id: DefId,
) -> Option<DefId> {
    tcx.impl_of_method(trait_method_def_id)
}

pub fn resolve_trait_impl_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_did: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<DefId> {
    let param_env = tcx.param_env(callee_did);

    if let Ok(normalized_substs) = tcx.try_normalize_erasing_regions(param_env, substs) {
        if let Ok(Some(instance)) = Instance::resolve(tcx, param_env, callee_did, normalized_substs) {
            Some(instance.def_id())
        } else {
            None
        }
    } else {
        None 
    }
}

pub fn extract_ty_def_id<'tcx>(ty: Ty<'tcx>) -> Option<DefId> {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => Some(adt_def.did()),
        TyKind::Ref(_, inner_ty, _) => extract_ty_def_id(*inner_ty),
        TyKind::RawPtr(ty_mut) => extract_ty_def_id(ty_mut.ty),
        _ => None,
    }
}

pub fn has_static_bound<'tcx>(tcx: TyCtxt<'tcx>, function_id: DefId) -> bool {
    let param_env = tcx.param_env(function_id);
    // progress_info!("caller bounds: {:?}", param_env.caller_bounds());
    for predicate in param_env.caller_bounds() {
        // progress_info!("pred: {:?}", predicate.to_string());
        if predicate.to_string().contains("'static") {
            return true;
        }
    }
    false
}