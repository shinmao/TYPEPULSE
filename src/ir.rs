//! Reduced MIR intended to cover many common use cases while keeping the analysis pipeline manageable.
//! Note that this is a translation of non-monomorphized, generic MIR.

use std::borrow::Cow;

use rustc_hir::def_id::DefId;
use rustc_index::{IndexVec, IndexSlice};
use rustc_middle::{
    mir,
    ty::{subst::SubstsRef, Ty},
};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::collections::{HashMap, HashSet};

// Efficient representation of type conversions within a function
// type conversion: source -> dest
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct TypeConversionMap<'tcx> {
    source_to_dest: FxHashMap<Ty<'tcx>, FxHashSet<Ty<'tcx>>>,
    dest_to_source: FxHashMap<Ty<'tcx>, FxHashSet<Ty<'tcx>>>,
}

impl<'tcx> TypeConversionMap<'tcx> {
    // Add a type conversion
    pub fn add_conversion(&mut self, source: Ty<'tcx>, dest: Ty<'tcx>) {
        self.source_to_dest
            .entry(source)
            .or_default()
            .insert(dest);
        self.dest_to_source
            .entry(dest)
            .or_default()
            .insert(source);
    }

    // The function is used after ReturnMap::get_func_by_ret_ty
    // which are defid of constructor function
    // Given each DefId, the function will return a list of source type, which converts to the ret_ty
    // if else, return None
    pub fn get_constructor_source(&self, ret_ty: Ty<'tcx>) -> Option<Vec<Ty<'tcx>>> {
        let mut res = Vec::new();
        let constructed_source = if self.dest_to_source.contains_key(&ret_ty) {
            // there are source type, which can convert to ret_ty
            for rt in &self.dest_to_source[&ret_ty] {
                res.push(*rt);
            }
            Some(res)
        } else {
            None
        };
        
        constructed_source
    }
}

// Represents a function in the call graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionData<'tcx> {
    pub id: DefId,
    pub callers: HashSet<DefId>,
    pub type_conversions: TypeConversionMap<'tcx>,
    pub type_check: HashSet<String>,
    pub ret_ty: HashSet<Ty<'tcx>>,
}

impl FunctionData<'_> {
    pub fn new(fid: DefId) -> Self {
        Self {
            id: fid,
            callers: HashSet::new(),
            type_conversions: TypeConversionMap::default(),
            type_check: HashSet::new(),
            ret_ty: HashSet::new(),
        }
    }
}

#[derive(Debug)]
pub struct Terminator<'tcx> {
    pub kind: TerminatorKind<'tcx>,
    pub original: mir::Terminator<'tcx>,
}

// https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/mir/syntax/enum.TerminatorKind.html
#[derive(Debug)]
pub enum TerminatorKind<'tcx> {
    Goto(usize),
    Return,
    StaticCall {
        callee_did: DefId,
        callee_substs: SubstsRef<'tcx>,
        args: Vec<mir::Operand<'tcx>>,
        dest: mir::Place<'tcx>,
    },
    FnPtr {
        value: mir::ConstantKind<'tcx>,
    },
    Unimplemented(Cow<'static, str>),
}

#[derive(Debug)]
pub struct BasicBlock<'tcx> {
    pub statements: Vec<mir::Statement<'tcx>>,
    pub terminator: Terminator<'tcx>,
    pub is_cleanup: bool,
}

#[derive(Debug)]
pub struct LocalDecl<'tcx> {
    pub ty: Ty<'tcx>,
}

#[derive(Debug)]
pub struct Body<'tcx> {
    pub local_decls: Vec<LocalDecl<'tcx>>,
    pub original_decls: IndexVec<mir::Local, mir::LocalDecl<'tcx>>,
    pub basic_blocks: Vec<BasicBlock<'tcx>>,
    pub original: mir::Body<'tcx>,
    pub place_neighbor_list: Vec<Vec<usize>>,
}

impl<'tcx> mir::HasLocalDecls<'tcx> for Body<'tcx> {
    fn local_decls(&self) -> &IndexSlice<mir::Local, mir::LocalDecl<'tcx>> {
        &self.original_decls.as_slice()
    }
}


impl<'tcx> Body<'tcx> {
    pub fn arg_cnt(&self) -> usize {
        self.original.arg_count
    }

    pub fn statements(&self) -> Vec<mir::Statement<'tcx>> {
        let mut statement_list: Vec<mir::Statement<'tcx>> = Vec::new();
        for block in &self.basic_blocks {
            for st in &block.statements {
                statement_list.push(st.clone());
            }
        }
        statement_list
    }

    pub fn terminators(&self) -> impl Iterator<Item = &Terminator<'tcx>> {
        self.basic_blocks.iter().map(|block| &block.terminator)
    }

    pub fn basic_blocks(&self) -> impl Iterator<Item = &BasicBlock<'tcx>> {
        self.basic_blocks.iter()
    }

    // copied from mir::Body
    pub fn local_kind(&self, local: mir::Local) -> u8 {
        let index = local.as_usize();
        if index == 0 {
            0
        } else if index < self.original.arg_count + 1 {
            1
        } else {
            2
        }
    }
}
