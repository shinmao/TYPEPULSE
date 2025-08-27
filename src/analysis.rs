mod broken_layout;
mod uninit_exposure;
mod broken_bitpatterns;

use rustc_hir::{ItemKind, ImplPolarity, ItemId, hir_id::OwnerId, OwnerNode};
use rustc_middle::hir::Owner;
use rustc_middle::ty::{self, Ty, ParamEnv, TypeAndMut, TyKind, TyCtxt, IntTy, UintTy, FloatTy, TraitPredicate, Binder};

use snafu::{Error, ErrorCompat};

use crate::report::ReportLevel;
use crate::context::TypePulseCtxt;
use crate::progress_info;

use std::collections::HashSet;

pub use broken_layout::{BehaviorFlag as BrokenLayoutBehaviorFlag, BrokenLayoutChecker};
pub use uninit_exposure::{BehaviorFlag as UninitExposureBehaviorFlag, UninitExposureChecker};
pub use broken_bitpatterns::{BehaviorFlag as BrokenBitPatternsBehaviorFlag, BrokenBitPatternsChecker};

pub type AnalysisResult<'tcx, T> = Result<T, Box<dyn AnalysisError + 'tcx>>;

use std::borrow::Cow;

pub trait AnalysisError: Error + ErrorCompat {
    fn kind(&self) -> AnalysisErrorKind;
    fn log(&self) {
        match self.kind() {
            AnalysisErrorKind::Unreachable => {
                error!("[{:?}] {}", self.kind(), self);
                if cfg!(feature = "backtraces") {
                    if let Some(backtrace) = ErrorCompat::backtrace(self) {
                        error!("Backtrace:\n{:?}", backtrace);
                    }
                }
            }
            AnalysisErrorKind::Unimplemented => {
                info!("[{:?}] {}", self.kind(), self);
                if cfg!(feature = "backtraces") {
                    if let Some(backtrace) = ErrorCompat::backtrace(self) {
                        info!("Backtrace:\n{:?}", backtrace);
                    }
                }
            }
            AnalysisErrorKind::OutOfScope => {
                debug!("[{:?}] {}", self.kind(), self);
                if cfg!(feature = "backtraces") {
                    if let Some(backtrace) = ErrorCompat::backtrace(self) {
                        debug!("Backtrace:\n{:?}", backtrace);
                    }
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AnalysisErrorKind {
    /// An error that should never happen;
    /// If this happens, that means some of our assumption / invariant is broken.
    /// Normal programs would panic for it, but we want to avoid panic at all cost,
    /// so this error exists.
    Unreachable,
    /// A pattern that is not handled by our algorithm yet.
    Unimplemented,
    /// An expected failure, something like "we don't handle this by design",
    /// that worth recording.
    OutOfScope,
}

#[derive(Debug, Copy, Clone)]
pub enum AnalysisKind {
    BrokenLayout(BrokenLayoutBehaviorFlag),
    UninitExposure(UninitExposureBehaviorFlag),
    BrokenBitPatterns(BrokenBitPatternsBehaviorFlag),
}

trait IntoReportLevel {
    fn report_level(&self, visibility: bool) -> ReportLevel;
}

impl Into<Cow<'static, str>> for AnalysisKind {
    fn into(self) -> Cow<'static, str> {
        match &self {
            AnalysisKind::BrokenLayout(bypass_kinds) => {
                let mut v = vec!["BrokenLayout:"];
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::READ_FLOW) {
                //     v.push("ReadFlow")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::COPY_FLOW) {
                //     v.push("CopyFlow")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::VEC_FROM_RAW) {
                //     v.push("VecFromRaw")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::TRANSMUTE) {
                //     v.push("Transmute")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::WRITE_FLOW) {
                //     v.push("WriteFlow")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::PTR_AS_REF) {
                //     v.push("PtrAsRef")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::SLICE_UNCHECKED) {
                //     v.push("SliceUnchecked")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::SLICE_FROM_RAW) {
                //     v.push("SliceFromRaw")
                // }
                // if bypass_kinds.contains(BrokenLayoutBehaviorFlag::VEC_SET_LEN) {
                //     v.push("VecSetLen")
                // }
                v.join("/").into()
            },
            AnalysisKind::UninitExposure(bypass_kinds) => {
                let mut v = vec!["UninitExposure:"];
                v.join("/").into()
            },
            AnalysisKind::BrokenBitPatterns(bypass_kinds) => {
                let mut v = vec!["BrokenBitPatterns:"];
                v.join("/").into()
            },
        }
    }
}

// e.g., A is less than B
// A is equal to B
// A is greater than B
// In the case of NoideaG, A >= B
// In the case of NoideaL, A <= B
#[derive(Debug, Copy, Clone)]
pub enum Comparison {
    Less,
    Equal,
    Greater,
    Noidea,
    NoideaG,
    NoideaL,
}

pub struct LayoutChecker<'tcx> {
    rcx: TypePulseCtxt<'tcx>,
    from_ty: Ty<'tcx>,
    to_ty: Ty<'tcx>,
    fty_layout: bool,
    tty_layout: bool,
    align_status: Comparison,
    size_status: Comparison,
    ty_bnd: HashSet<Ty<'tcx>>,
}

// LayoutChecker can help us get the align/size status of type conversion
// take one exception case for target into consideration
// on x86 u64 and f64 are only aligned to 4 bytes
impl<'tcx> LayoutChecker<'tcx> {
    pub fn new(rc: TypePulseCtxt<'tcx>, p_env: ParamEnv<'tcx>, f_ty: Ty<'tcx>, t_ty: Ty<'tcx>) -> Self {
        // optimization option to call trait checker
        let opt_option = rc.opt_option();

        // progress_info!("LayoutChecker- from_ty:{:?}, to_ty:{:?}", f_ty, t_ty);
        let (mut f_layout, mut t_layout) = (false, false);
        // rustc_middle::ty::TyCtxt
        let tcx = rc.tcx();
        let (f_ty_, t_ty_) = (get_pointee(f_ty), get_pointee(t_ty));
        
        let ty_bnd = if opt_option == true {
            let tc = GenericChecker::new(rc, p_env, f_ty_, t_ty_);
            tc.get_satisfied_ty()
        } else {
            let empty_ty_set: HashSet<Ty<'tcx>> = HashSet::new();
            empty_ty_set
        };

        // try to handle external type if we can't get type information
        let mut ext_fty_info: u64 = 0;
        let mut ext_tty_info: u64 = 0;
        if let Err(_) = tcx.layout_of(p_env.and(f_ty_)) {
            match get_external(tcx, f_ty_) {
                Some(external_ty) => {
                    ext_fty_info = external_ty;
                },
                None => {},
            }
        }
        if let Err(_) = tcx.layout_of(p_env.and(t_ty_)) {
            match get_external(tcx, t_ty_) {
                Some(external_ty) => {
                    ext_tty_info = external_ty;
                },
                None => {},
            }
        }
        // from_ty_and_layout = rustc_target::abi::TyAndLayout
        // (align_status, size_status)
        let layout_res = if let Ok(from_ty_and_layout) = tcx.layout_of(p_env.and(f_ty_))
            && let Ok(to_ty_and_layout) = tcx.layout_of(p_env.and(t_ty_))
        {
            // progress_info!("Both layout are known");
            // in this case, only align_status == Comparison::Less will warn
            f_layout = true;
            t_layout = true;
            let (from_layout, to_layout) = (from_ty_and_layout.layout, to_ty_and_layout.layout);
            let (from_align, to_align) = (from_layout.align(), to_layout.align());
            let (from_size, to_size) = (from_layout.size(), to_layout.size());
            // for align_status
            // progress_info!("LayoutChecker- from_align:{}, to_align:{}", from_align.abi.bytes(), to_align.abi.bytes());
            let mut ag_status = if from_align.abi.bytes() < to_align.abi.bytes() {
                Comparison::Less
            } else if from_align.abi.bytes() == to_align.abi.bytes() {
                Comparison::Equal
            } else if from_align.abi.bytes() > to_align.abi.bytes() {
                Comparison::Greater
            } else {
                Comparison::Noidea
            };

            // exception cases for u64 and f64
            match ag_status {
                Comparison::Less => {},
                _ => {
                    // check type kind of from_ty
                    match f_ty_.kind() {
                        TyKind::Uint(uint_ty) => {
                            // u64
                            if (uint_ty.name_str() == "u64") && (4 < to_align.abi.bytes()) {
                                // progress_info!("from_align could be :{} on x86", 4);
                                ag_status = Comparison::Less;
                            }
                        },
                        TyKind::Float(float_ty) => {
                            // f64
                            if (float_ty.name_str() == "f64") && (4 < to_align.abi.bytes()) {
                                // progress_info!("from_align could be :{} on x86", 4);
                                ag_status = Comparison::Less;
                            }
                        },
                        _ => {},
                    }
                },
            }
            // if to_ty is usize, then take the case away
            // or from_ty is c_void, also take the case away
            // or from zero-sized type
            if t_ty_.to_string() == "usize" || f_ty_.is_c_void(tcx) || from_size.bytes() == 0 {
                ag_status = Comparison::Noidea;
            }
            if to_align.abi.bytes() == 1 {
                ag_status = Comparison::NoideaG;
            }
            // progress_info!("LayoutChecker- from_size:{}, to_size:{}", from_size.bytes(), to_size.bytes());
            // for size_status
            let sz_status = if from_size.bytes() < to_size.bytes() {
                Comparison::Less
            } else if from_size.bytes() == to_size.bytes() {
                Comparison::Equal
            } else if from_size.bytes() > to_size.bytes() {
                Comparison::Greater
            } else {
                Comparison::Noidea
            };

            (ag_status, sz_status)
        } else if let Ok(from_ty_and_layout) = tcx.layout_of(p_env.and(f_ty_)) {
            // progress_info!("Only from ty layout is known");
            f_layout = true;
            // we can only identify from_ty's layout
            let from_layout = from_ty_and_layout.layout;
            let from_align = from_layout.align();
            let from_size = from_layout.size();
            let mut ag_status = if let TyKind::Param(_) = t_ty_.kind() {
                // progress_info!("generic type conversion");
                // in this case, we can't get layout because t_ty_ is generic type
                // call GenericChecker for help
                let is_wrapped = f_ty_.contains(t_ty_);
                if !is_wrapped {
                    if ty_bnd.len() == 0 {
                        // t_ty_ could be arbitrary types
                        Comparison::Less
                    } else {
                        // t_ty_ is limited to trait bound
                        let mut res = Comparison::Noidea;
                        for satisfied_ty in &ty_bnd {
                            let sub_lc = LayoutChecker::new(rc, p_env, f_ty_, *satisfied_ty);
                            let sub_align_status = sub_lc.get_align_status();
                            match sub_align_status {
                                Comparison::Less => {
                                    res = Comparison::Less;
                                    break;
                                },
                                _ => {},
                            }
                        }
                        res
                    }
                } else {
                    Comparison::Equal
                }
            } else {
                // we can't get layout because t_ty_ might be external type
                // apply heuristics
                let mut res = Comparison::Noidea;
                if ext_tty_info != 0 {
                    // we have some type info of to_ty
                    if from_align.abi.bytes() < ext_tty_info {
                        res = Comparison::Less;
                    } else if from_align.abi.bytes() == ext_tty_info {
                        res = Comparison::Equal;
                    } else {
                        res = Comparison::Greater;
                    }
                } else {
                    if from_align.abi.bytes() == 1 {
                        res = Comparison::NoideaL;
                    } else {
                        res = Comparison::Noidea;
                    }
                }
                res
            };

            if f_ty_.is_c_void(tcx) || f_ty_.to_string() == "usize" || from_size.bytes() == 0 {
                ag_status = Comparison::Noidea;
            }
            
            let sz_status = if from_size.bytes() == 1 {
                Comparison::NoideaL
            } else {
                Comparison::Noidea
            };

            (ag_status, sz_status)
        } else if let Ok(to_ty_and_layout) = tcx.layout_of(p_env.and(t_ty_)) {
            // progress_info!("Only to ty layout is known");
            t_layout = true;
            // we can only identify to_ty's layout
            let to_layout = to_ty_and_layout.layout;
            let to_align = to_layout.align();
            let to_size = to_layout.size();
            let mut ag_status = if let TyKind::Param(_) = f_ty_.kind() {
                // progress_info!("generic type conversion");
                // f_ty_ is generic type
                // call GenericChecker for help
                let is_wrapped = t_ty_.contains(f_ty_);
                if !is_wrapped {
                    if ty_bnd.len() == 0 {
                        // f_ty_ could be arbitrary types
                        if to_align.abi.bytes() == 1 {
                            Comparison::NoideaG
                        } else {
                            Comparison::Less
                        }
                    } else {
                        // f_ty_ is limited to trait bound
                        let mut res = Comparison::Noidea;
                        for satisfied_ty in &ty_bnd {
                            let sub_lc = LayoutChecker::new(rc, p_env, *satisfied_ty, t_ty_);
                            let sub_align_status = sub_lc.get_align_status();
                            match sub_align_status {
                                Comparison::Less => {
                                    res = Comparison::Less;
                                    break;
                                },
                                _ => {},
                            }
                        }
                        res
                    }
                } else {
                    Comparison::Equal
                }
            } else {
                // we can't identify f_ty layout not because genric type
                // try applying heuristics
                let mut res = Comparison::Noidea;
                if ext_fty_info != 0 {
                    if ext_fty_info < to_align.abi.bytes() {
                        res = Comparison::Less;
                    } else if ext_fty_info == to_align.abi.bytes() {
                        res = Comparison::Equal;
                    } else {
                        res = Comparison::Greater;
                    }
                } else {
                    if to_align.abi.bytes() == 1 {
                        res = Comparison::NoideaG;
                    } else {
                        res = Comparison::Noidea;
                    }
                }
                res
            };
            

            if t_ty_.to_string() == "usize" {
                ag_status = Comparison::Noidea;
            }

            let sz_status = if to_size.bytes() == 1 {
                Comparison::NoideaG
            } else {
                Comparison::Noidea
            };

            (ag_status, sz_status)
        } else {
            // progress_info!("Both layout are unknown");
            (Comparison::Noidea, Comparison::Noidea)
        };

        LayoutChecker { rcx: rc, 
            from_ty: f_ty_, 
            to_ty: t_ty_,
            fty_layout: f_layout,
            tty_layout: t_layout,
            align_status: layout_res.0,
            size_status: layout_res.1,
            ty_bnd: ty_bnd.clone(),
        }
    }

    pub fn get_align_status(&self) -> Comparison {
        self.align_status
    }

    pub fn get_size_status(&self) -> Comparison {
        self.size_status
    }

    pub fn get_ty_bnd(&self) -> HashSet<Ty<'tcx>> {
        self.ty_bnd.clone()
    }

    pub fn get_from_ty(&self) -> Ty<'tcx> {
        self.from_ty
    }

    pub fn get_to_ty(&self) -> Ty<'tcx> {
        self.to_ty
    }

    pub fn is_fty_layout_spec(&self) -> bool {
        self.fty_layout
    }

    pub fn is_tty_layout_spec(&self) -> bool {
        self.tty_layout
    }

    pub fn get_from_ty_name(&self) -> String {
        self.from_ty.to_string()
    }

    pub fn get_to_ty_name(&self) -> String {
        self.to_ty.to_string()
    }

    pub fn is_from_to_primitive(&self) -> (bool, bool) {
        (self.from_ty.is_primitive_ty(), self.to_ty.is_primitive_ty())
    }

    pub fn is_from_to_arr_slice(&self) -> (bool, bool) {
        (self.from_ty.is_array_slice(), self.to_ty.is_array_slice())
    }

    pub fn is_from_to_adt(&self) -> (bool, bool) {
        (self.from_ty.is_adt(), self.to_ty.is_adt())
    }

    pub fn is_from_to_zero_tuple(&self) -> (bool, bool) {
        let is_from = if let TyKind::Tuple(ty_list) = self.from_ty.kind() {
            ty_list.len() == 0
        } else {
            false
        };

        let is_to = if let TyKind::Tuple(ty_list) = self.to_ty.kind() {
            ty_list.len() == 0
        } else {
            false
        };

        (is_from, is_to)
    }

    pub fn is_from_to_transparent(&self) -> (bool, bool) {
        let is_from = if let TyKind::Adt(def, _) = self.from_ty.kind() {
            def.repr().transparent()
        } else {
            false
        };

        let is_to = if let TyKind::Adt(def, _) = self.to_ty.kind() {
            def.repr().transparent()
        } else {
            false
        };

        (is_from, is_to)
    }

    pub fn is_from_to_c(&self) -> (bool, bool) {
        let is_from = if let TyKind::Adt(def, _) = self.from_ty.kind() {
            def.repr().c()
        } else {
            false
        };

        let is_to = if let TyKind::Adt(def, _) = self.to_ty.kind() {
            def.repr().c()
        } else {
            false
        };

        (is_from, is_to)
    }

    pub fn is_from_to_generic(&self) -> (bool, bool) {
        let is_from_generic = match self.from_ty.kind() {
            TyKind::Param(_) => {
                true
            },
            _ => { false },
        };
        let is_to_generic = match self.to_ty.kind() {
            TyKind::Param(_) => {
                true
            },
            _ => { false },
        };
        (is_from_generic, is_to_generic)
    }

    pub fn is_from_to_foreign(&self) -> (bool, bool) {
        let is_from_foreign = match self.from_ty.kind() {
            TyKind::Foreign(_) => { true },
            _ => { false },
        };
        let is_to_foreign = match self.to_ty.kind() {
            TyKind::Foreign(_) => { true },
            _ => { false },
        };
        (is_from_foreign, is_to_foreign)
    }

    pub fn is_from_to_dyn(&self) -> (bool, bool) {
        let is_from_dyn = self.from_ty.is_trait() | self.from_ty.is_dyn_star();
        let is_to_dyn = self.to_ty.is_trait() | self.to_ty.is_dyn_star();
        (is_from_dyn, is_to_dyn)
    }
}

// get the pointee or wrapped type
pub fn get_pointee(matched_ty: Ty<'_>) -> Ty<'_> {
    // progress_info!("get_pointee: > {:?} as type: {:?}", matched_ty, matched_ty.kind());
    let pointee = if let ty::RawPtr(ty_mut) = matched_ty.kind() {
        get_pointee(ty_mut.ty)
    } else if let ty::Ref(_, referred_ty, _) = matched_ty.kind() {
        get_pointee(*referred_ty)
    } else {
        matched_ty
    };
    pointee
}

// try to get external type
// only try to handle primitive type
fn get_external<'tcx>(tcx: TyCtxt<'tcx>, matched_ty: Ty<'tcx>) -> Option<u64>{
    let ty_symbol = matched_ty.to_string();
    if ty_symbol.contains("bool") || ty_symbol.contains("i8") || ty_symbol.contains("u8") {
        Some(1)
    } else if ty_symbol.contains("i16") || ty_symbol.contains("u16") {
        Some(2)
    } else if ty_symbol.contains("i32") || ty_symbol.contains("u32") || ty_symbol.contains("f32") || ty_symbol.contains("char") {
        Some(4)
    } else if ty_symbol.contains("u64") || ty_symbol.contains("i64") || ty_symbol.contains("f64") {
        Some(8)
    } else if ty_symbol.contains("u128") || ty_symbol.contains("i128") {
        Some(16)
    } else {
        None
    }
}

// Used for type conversion pair in ty_bnd
// Others: arbitrary types
#[derive(Debug, Copy, Clone)]
pub enum SatisfiedPair {
    Adt2Adt,
    Adt2Prime,
    Adt2ArrSlice,
    Dyn2Adt,
    Others,
}

pub struct SatisfiedChecker {
    consistent_status: SatisfiedPair,
}

impl<'tcx> SatisfiedChecker {
    pub fn new(lc: &LayoutChecker<'tcx>) -> Self {
        // let tcx = rc.tcx();
        // let lc = LayoutChecker::new(rc, p_env, f_ty, t_ty);
        let from_ty = lc.get_from_ty();
        let to_ty = lc.get_to_ty();
        let ty_bnd = lc.get_ty_bnd();

        let (from_gen, to_gen) = lc.is_from_to_generic();

        let (is_from_prime, is_to_prime) = lc.is_from_to_primitive();
        let (is_from_adt, is_to_adt) = lc.is_from_to_adt();
        let (is_from_gen, is_to_gen) = lc.is_from_to_generic();
        let (is_from_arr_slice, is_to_arr_slice) = lc.is_from_to_arr_slice();
        let (is_from_foreign, is_to_foreign) = lc.is_from_to_foreign();
        let (is_from_trans, is_to_trans) = lc.is_from_to_transparent();
        let (is_from_c, is_to_c) = lc.is_from_to_c();
        let (is_from_dyn, is_to_dyn) = lc.is_from_to_dyn();
        let (is_from_tuple, is_to_tuple) = lc.is_from_to_zero_tuple();

        // Adt > Adt
        // Adt > Prime
        // Adt > Arr/Slice

        let mut consistent_status = SatisfiedPair::Others;

        for satisfied_ty in ty_bnd {
            let sty = get_pointee(satisfied_ty);
            if from_gen && !to_gen {
                // generic > concrete
                if sty.is_adt() && is_to_adt {
                    consistent_status = SatisfiedPair::Adt2Adt;
                    break;
                } else if sty.is_adt() && is_to_prime {
                    consistent_status = SatisfiedPair::Adt2Prime;
                    break;
                } else if sty.is_adt() && is_to_arr_slice {
                    consistent_status = SatisfiedPair::Adt2ArrSlice;
                    break;
                }
            } else if !from_gen && to_gen {
                // concrete > generic
                if is_from_adt && sty.is_adt() {
                    consistent_status = SatisfiedPair::Adt2Adt;
                    break;
                } else if is_from_adt && sty.is_primitive_ty() {
                    consistent_status = SatisfiedPair::Adt2Prime;
                    break;
                } else if is_from_adt && sty.is_array_slice() {
                    consistent_status = SatisfiedPair::Adt2ArrSlice;
                    break;
                } 
            }
        };

        SatisfiedChecker { 
            consistent_status: consistent_status,
        }
    }

    pub fn get_consistent_status(&self) -> SatisfiedPair {
        self.consistent_status
    }
}

pub struct ValueChecker<'tcx> {
    rcx: TypePulseCtxt<'tcx>,
    from_ty: Ty<'tcx>,
    to_ty: Ty<'tcx>,
    value_status: Comparison,
}

impl<'tcx> ValueChecker<'tcx> {
    pub fn new(rc: TypePulseCtxt<'tcx>, p_env: ParamEnv<'tcx>, f_ty: Ty<'tcx>, t_ty: Ty<'tcx>) -> Self {
        let tcx = rc.tcx();
        let lc = LayoutChecker::new(rc, p_env, f_ty, t_ty);
        let from_ty = lc.get_from_ty();
        let to_ty = lc.get_to_ty();
        let from_mutable = f_ty.is_mutable_ptr();
        let to_mutable = t_ty.is_mutable_ptr();
        let ty_bnd = lc.get_ty_bnd();
        
        let (from_gen, to_gen) = lc.is_from_to_generic();

        // we only focus on the type conversion between generic and concrete type
        // compare the range of value set to get the size status
        // progress_info!("from_ty is c_void? {}", from_ty.is_c_void(tcx));
        // progress_info!("to_ty is c_void? {}", to_ty.is_c_void(tcx));
        let is_from_c_void = from_ty.to_string().contains("c_void");
        let is_to_c_void = to_ty.to_string().contains("c_void");
        let mut val_status = if (from_gen == true || is_from_c_void) && (to_gen == false && !is_to_c_void) {
            // progress_info!("ValueChecker: generic > concrete");
            // is from_ty wrapped in to_ty?
            let is_wrapped = to_ty.contains(from_ty);
            if !is_wrapped {
                if ty_bnd.len() == 0 {
                    // from_ty could be arbitrary type
                    if to_ty.is_bool() || to_ty.is_str() || to_ty.is_char() || to_ty.is_enum() {
                        // to_ty is more constrainted
                        Comparison::Less
                    } else if to_ty.is_numeric() || to_ty.is_str() || to_ty.is_char() {
                        // to_ty can be type with no limit
                        Comparison::Greater
                    } else {
                        Comparison::Noidea
                    }
                } else {
                    let mut res = Comparison::Noidea;
                    for satisfied_ty in ty_bnd {
                        let satisfied_sym = satisfied_ty.to_string().to_lowercase();
                        let unicode_sym = "unicode";
                        let utf8_sym = "utf8";
                        let str_sym = "string";
                        if (satisfied_ty.is_numeric() || satisfied_ty.is_str() || satisfied_ty.is_char())
                            && (to_ty.is_bool() || to_ty.is_str() || to_ty.is_char() || to_ty.is_enum()) {
                            res = Comparison::Less;
                            break;
                        } else if (satisfied_ty.is_bool() || satisfied_ty.is_str() || satisfied_ty.is_char() || satisfied_ty.is_enum())
                            && (to_ty.is_numeric() || to_ty.is_str() || to_ty.is_char()) {
                                if to_mutable {
                                    res = Comparison::Greater;
                                    break;
                                }
                        }
                    }
                    res
                }
            } else {
                Comparison::Equal
            }
        } else if from_gen == false && to_gen == true {
            // progress_info!("ValueChecker: concrete > generic");
            let is_wrapped = from_ty.contains(to_ty);
            if !is_wrapped {
                if ty_bnd.len() == 0 {
                    // to_ty could be arbitrary type
                    if from_ty.is_numeric() || from_ty.is_str() || from_ty.is_char() {
                        Comparison::Less
                    } else if from_ty.is_bool() || from_ty.is_str() || from_ty.is_char() || from_ty.is_enum() {
                        Comparison::Greater
                    } else {
                        Comparison::Noidea
                    }
                } else {
                    let mut res = Comparison::Noidea;
                    for satisfied_ty in ty_bnd {
                        if (from_ty.is_numeric() || from_ty.is_str() || from_ty.is_char())
                            && (satisfied_ty.is_bool() || satisfied_ty.is_str() || satisfied_ty.is_char() || satisfied_ty.is_enum()) {
                            res = Comparison::Less;
                            break;
                        } else if (from_ty.is_bool() || from_ty.is_str() || from_ty.is_char() || from_ty.is_enum())
                            && (satisfied_ty.is_numeric() || satisfied_ty.is_str() || satisfied_ty.is_char()) {
                                if to_mutable {
                                    res = Comparison::Greater;
                                    break;
                                }
                        }
                    }
                    res
                }
            } else {
                Comparison::Equal
            }
        } else {
            if from_ty.is_array_slice() {
                match from_ty.kind() {
                    TyKind::Array(ety, _) | TyKind::Slice(ety) => {
                        if (ety.is_numeric() || ety.is_str() || ety.is_char()) &&
                            (to_ty.is_bool() || to_ty.is_str() || to_ty.is_char() || to_ty.is_enum()) {
                            Comparison::Less
                        } else if (ety.is_bool() || ety.is_str() || ety.is_char() || ety.is_enum()) &&
                            (to_ty.is_numeric() || to_ty.is_str() || to_ty.is_char()) {
                            Comparison::Greater
                        } else {
                            Comparison::Noidea
                        }
                    },
                    _ => { Comparison::Noidea },
                }
            } else if to_ty.is_array_slice() {
                match to_ty.kind() {
                    TyKind::Array(ety, _) | TyKind::Slice(ety) => {
                        if (from_ty.is_numeric() || from_ty.is_str() || from_ty.is_char()) &&
                            (ety.is_bool() || ety.is_str() || ety.is_char() || ety.is_enum()) {
                            Comparison::Less
                        } else if (from_ty.is_bool() || from_ty.is_str() || from_ty.is_char() || from_ty.is_enum()) &&
                            (ety.is_numeric() || ety.is_str() || ety.is_char()) {
                            Comparison::Greater
                        } else {
                            Comparison::Noidea
                        }
                    },
                    _ => { Comparison::Noidea },
                }
            } else {
                if (from_ty.is_numeric() || from_ty.is_str() || from_ty.is_char()) &&
                    (to_ty.is_bool() || to_ty.is_str() || to_ty.is_char() || to_ty.is_enum()) {
                    Comparison::Less
                } else if (from_ty.is_bool() || from_ty.is_str() || from_ty.is_char() || from_ty.is_enum()) &&
                    (to_ty.is_numeric() || to_ty.is_str() || to_ty.is_char()) {
                    Comparison::Greater
                } else {
                    Comparison::Noidea
                }
            }
        };

        match val_status {
            Comparison::Noidea => {
                if (from_gen || is_from_c_void) && (!to_gen && !is_to_c_void) {
                    if to_ty.to_string().contains("u8") {
                        val_status = Comparison::NoideaG;
                    }
                } else if !from_gen && to_gen {
                    if from_ty.is_bool() {
                        val_status = Comparison::NoideaG;
                    } 
                } else {
                    if to_ty.to_string().contains("u8") || from_ty.is_bool() {
                        val_status = Comparison::NoideaG;
                    }
                }
            },
            _ => {},
        }

        if is_to_c_void || from_ty.to_string().contains("MaybeUninit") {
            val_status = Comparison::Noidea;
        }

        ValueChecker { rcx: rc, 
            from_ty: from_ty, 
            to_ty: to_ty,
            value_status: val_status,
        }
    }

    pub fn get_val_status(&self) -> Comparison {
        self.value_status
    }
}

pub struct GenericChecker<'tcx> {
    rcx: TypePulseCtxt<'tcx>,
    trait_set: HashSet<Ty<'tcx>>,
}

impl<'tcx> GenericChecker<'tcx> {
    pub fn new(rc: TypePulseCtxt<'tcx>, p_env: ParamEnv<'tcx>, from_ty: Ty<'tcx>, to_ty: Ty<'tcx>) -> Self {
        let tcx = rc.tcx();
        let hir = tcx.hir();

        let mut trait_bnd_set: HashSet<String> = HashSet::new();
        let mut satisfied_ty_set: HashSet<Ty<'tcx>> = HashSet::new();

        for cb in p_env.caller_bounds() {
            // cb: Binder(TraitPredicate(<Self as trait>, ..)
            // Focus on the trait bound applied to our generic parameter

            if let Some(trait_pred) = cb.to_opt_poly_trait_pred() {
                let trait_def_id = trait_pred.def_id();
                let trait_name = tcx.def_path_str(trait_def_id);
                trait_bnd_set.insert(trait_name.clone());
                // progress_info!("current trait name: ({})", trait_name);

                // for each implementation
                for &impl_id in hir.trait_impls(trait_def_id) {
                    // impl_id: LocalDefId
                    let impl_owner_id = hir.expect_owner(impl_id).def_id();
                    let item = hir.item(ItemId { owner_id: impl_owner_id});
                    if_chain! {
                        if let ItemKind::Impl(impl_item) = item.kind;
                        if impl_item.polarity == ImplPolarity::Positive;
                        if let Some(binder) = tcx.impl_trait_ref(impl_id);
                        then {
                            let trait_ref = binder.skip_binder();
                            let impl_ty = trait_ref.self_ty();
                            match impl_ty.kind() {
                                TyKind::Adt(adt_def, impl_trait_substs) => {
                                    let adt_did = adt_def.did();
                                    let adt_ty = tcx.type_of(adt_did).skip_binder();
                                    // progress_info!("{} is implemented on adt({:?})", trait_name, adt_ty);
                                    satisfied_ty_set.insert(adt_ty);
                                },
                                TyKind::Param(p_ty) => {
                                    let param_ty = p_ty.to_ty(tcx);
                                },
                                _ => {
                                    // progress_info!("{} is implemented on {:?}", trait_name, impl_ty);
                                    satisfied_ty_set.insert(impl_ty);
                                },
                            }
                        }
                    }
                }

                // handle known external trait e.g., Pod
                if trait_name == "bytemuck::Pod" || trait_name == "plain::Plain" {
                    let ty_bnd = Self::get_satisfied_ty_for_Pod(tcx);
                    satisfied_ty_set.extend(&ty_bnd);
                    // progress_info!("current trait bound type set: {:?}", satisfied_ty_set);
                }
            }
        }

        // check trait_bnd_set
        let std_trait_set = HashSet::from([
            String::from("std::marker::Copy"), 
            String::from("std::clone::Clone"), 
            String::from("std::marker::Sized")
        ]);
        // if all trait_bound is std::marker, then we could assume it to be arbitrary type
        // to avoid messing up with build type manually
        // we just clear the satisfied ty set
        if trait_bnd_set.is_subset(&std_trait_set) {
            satisfied_ty_set.clear();
        }

        // progress_info!("trait bound type set: {:?}", satisfied_ty_set);

        GenericChecker {
            rcx: rc,
            trait_set: satisfied_ty_set.clone(),
        }
    }

    pub fn get_satisfied_ty(&self) -> HashSet<Ty<'tcx>> {
        self.trait_set.clone()
    }

    fn get_satisfied_ty_for_Pod(tcx: TyCtxt<'tcx>) -> HashSet<Ty<'tcx>> {
        let mut satisfied_ty_set_for_pod: HashSet<Ty<'tcx>> = HashSet::new();
        // f64, u64, i8, i32, u8, i16, u16, u32, usize, i128, isize, i64, u128, f32
        let pod_ty = vec![
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::Isize)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I8)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I16)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I32)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I64)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I128)),

            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::Usize)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U8)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U16)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U32)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U64)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U128)),

            tcx.mk_ty_from_kind(TyKind::Float(FloatTy::F32)),
            tcx.mk_ty_from_kind(TyKind::Float(FloatTy::F64))
        ];

        for pt in pod_ty.iter() {
            satisfied_ty_set_for_pod.insert(*pt);
        }
        satisfied_ty_set_for_pod.clone()
    }
}
