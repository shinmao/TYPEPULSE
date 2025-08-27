use std::collections::{HashMap, HashSet};
use crate::ir::FunctionData;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir,
    ty::{subst::SubstsRef, Ty},
};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct CallGraph<'tcx> {
    pub functions: HashMap<DefId, FunctionData<'tcx>>, // Map of function ID to its data
    pub retmap: ReturnMap<'tcx>,
}

impl<'tcx> CallGraph<'tcx> {
    // Adds or updates a function in the graph
    pub fn add_function(&mut self, func_id: DefId) {
        self.functions.entry(func_id.clone()).or_insert_with(|| FunctionData::new(func_id.clone()));
    }

    // Records a call relationship
    pub fn add_caller(&mut self, callee_id: DefId, caller_id: DefId) {
        self.add_function(callee_id.clone());
        self.add_function(caller_id.clone());

        if let Some(callee_data) = self.functions.get_mut(&callee_id) {
            callee_data.callers.insert(caller_id);
        }
    }

    // Records a type conversion for a function
    pub fn add_type_conversion(&mut self, func_id: DefId, source: Ty<'tcx>, dest: Ty<'tcx>) {
        self.add_function(func_id.clone());

        if let Some(func_data) = self.functions.get_mut(&func_id) {
            func_data.type_conversions.add_conversion(source, dest);
        }
    }

    pub fn add_type_check(&mut self, func_id: DefId, check: String) {
        self.add_function(func_id.clone());

        if let Some(func_data) = self.functions.get_mut(&func_id) {
            func_data.type_check.insert(check);
        }
    }

    pub fn add_ret_ty(&mut self, func_id: DefId, ret_type: Ty<'tcx>) {
        self.add_function(func_id.clone());

        if let Some(func_data) = self.functions.get_mut(&func_id) {
            func_data.ret_ty.insert(ret_type);

            self.retmap.ret_ty_to_func
                .entry(ret_type)
                .or_default()
                .insert(func_id);
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ReturnMap<'tcx> {
    pub ret_ty_to_func: FxHashMap<Ty<'tcx>, FxHashSet<DefId>>,
}

impl<'tcx> ReturnMap<'tcx> {
    pub fn get_func_by_ret_ty(&self, ret_ty: Ty<'tcx>) -> Vec<DefId> {
        let mut res = Vec::new();
        if self.ret_ty_to_func.contains_key(&ret_ty) {
            for did in &self.ret_ty_to_func[&ret_ty] {
                res.push(*did);
            }
        }

        res
    }
}