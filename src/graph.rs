use std::{cmp::min, collections::VecDeque, collections::HashSet};

use crate::ir;

pub trait Graph {
    fn len(&self) -> usize;
    fn next(&self, id: usize) -> Vec<usize>;
}

impl<'tcx> Graph for ir::Body<'tcx> {
    fn len(&self) -> usize {
        // the count of all vars used at MIR level
        self.local_decls.len()
    }

    fn next(&self, id: usize) -> Vec<usize> {
        // next places of current place id
        unsafe { self.place_neighbor_list.get_unchecked(id).to_owned() }
    }
}

pub trait GraphTaint: Clone + Default {
    fn is_empty(&self) -> bool;
    fn contains(&self, taint: &Self) -> bool;
    fn join(&mut self, taint: &Self);
}

pub struct TaintAnalyzer<'a, G: Graph, T: GraphTaint> {
    graph: &'a G,
    len: usize,
    sources: Vec<T>,
    sinks: Vec<bool>,
}

impl<'a, G: Graph, T: GraphTaint> TaintAnalyzer<'a, G, T> {
    pub fn new(graph: &'a G) -> Self {
        let graph_len = graph.len();
        TaintAnalyzer {
            graph,
            len: graph_len,
            sources: vec![T::default(); graph_len],
            sinks: vec![false; graph_len],
        }
    }

    pub fn graph(&self) -> &G {
        &self.graph
    }

    pub fn mark_source(&mut self, id: usize, taint: &T) {
        self.sources[id].join(taint);
    }

    pub fn clear_source(&mut self, id: usize) {
        // use bfs to clean the tainted source
        let mut work_list = VecDeque::new();
        let mut visited = HashSet::new();

        work_list.push_back(id);
        visited.insert(id);
        while let Some(current) = work_list.pop_front() {
            for next in self.graph.next(current) {
                if !visited.contains(&next) {
                    work_list.push_back(next);
                    visited.insert(next);
                }
            }
        }

        for v in visited.iter() {
            self.sources[*v] = T::default();
        }
    }

    pub fn is_src_empty(&self, id: usize) -> bool {
        self.sources[id].is_empty()
    }

    pub fn is_all_src_empty(&self) -> bool {
        let mut is_cleared = true;
        for src in &self.sources {
            if src.is_empty() {
                is_cleared &= true;
            } else {
                is_cleared &= false;
            }
        }

        is_cleared
    }

    pub fn is_reachable(&self, start_id: usize, end_id: usize) -> bool {
        if start_id == end_id {
            return true;
        }
        
        let mut work_list = VecDeque::new();
        let mut visited = HashSet::new();

        work_list.push_back(start_id);
        visited.insert(start_id);
        while let Some(curr) = work_list.pop_front() {
            for next in self.graph.next(curr) {
                if next == end_id {
                    return true;
                }
                if !visited.contains(&next) {
                    work_list.push_back(next);
                    visited.insert(next);
                }
            }
        }

        false
    }

    pub fn mark_sink(&mut self, id: usize) {
        self.sinks[id] = true;
    }

    pub fn unmark_sink(&mut self, id: usize) {
        self.sinks[id] = false;
    }

    pub fn mark_at_once(&mut self, id: usize, taint: &T) {
        self.sources[id].join(taint);
        self.sinks[id] = true;
    }

    // Unmark all sources and sinks
    pub fn clear(&mut self) {
        self.sources = vec![T::default(); self.len];
        self.sinks = vec![false; self.len];
    }

    // Checks reachability between `self.sources` & `self.sinks`.
    pub fn propagate(&self) -> T {
        let mut taint_state = vec![T::default(); self.len];
        let mut work_list = VecDeque::new();

        // Initialize work list
        for id in 0..self.len {
            if !self.sources[id].is_empty() {
                taint_state[id].join(&self.sources[id]);
                work_list.push_back(id);
            }
        }

        // Breadth-first propagation
        while let Some(current) = work_list.pop_front() {
            for next in self.graph.next(current) {
                let mut next_state = std::mem::take(&mut taint_state[next]);
                let taint = &taint_state[current];
                if !next_state.contains(taint) {
                    next_state.join(taint);
                    work_list.push_back(next);
                }
                taint_state[next] = next_state;
            }
        }

        // Join all taints in the sink nodes
        let mut ret = T::default();
        for id in 0..self.len {
            if self.sinks[id] && !taint_state[id].is_empty() {
                ret.join(&taint_state[id]);
            }
        }

        return ret;
    }
}

/// Strongly Connected Component (SCC) using Tarjan's algorithm
pub struct Scc<'a, G: Graph> {
    graph: &'a G,
    /// group number of each item (indexed by node)
    group_of_node: Vec<usize>,
    /// nodes in each SCC group (indexed by group)
    nodes_in_group: Vec<Vec<usize>>,
    /// adjacency list of groups (indexed by group)
    group_graph: Vec<Vec<usize>>,
}

/// Temporary state variable used in SCC construction
struct SccConstructionState {
    // intermediate state
    current_index: usize,
    stack: Vec<usize>,
    index: Vec<usize>,
    // result
    group_of_node: Vec<usize>,
    nodes_in_group: Vec<Vec<usize>>,
}

impl SccConstructionState {
    fn new(size: usize) -> Self {
        SccConstructionState {
            current_index: 0,
            stack: Vec::new(),
            index: vec![0; size],
            group_of_node: vec![0; size],
            nodes_in_group: Vec::new(),
        }
    }

    fn assign_id(&mut self, node: usize) {
        self.current_index += 1;
        self.index[node] = self.current_index;
    }
}

struct SccTopologicalOrderState {
    visited: Vec<bool>,
    order: Vec<usize>,
}

impl SccTopologicalOrderState {
    fn new(size: usize) -> Self {
        SccTopologicalOrderState {
            visited: vec![false; size],
            order: Vec::new(),
        }
    }
}

impl<'a, G: Graph> Scc<'a, G> {
    pub fn construct(graph: &'a G) -> Self {
        let num_node = graph.len();
        let mut state = SccConstructionState::new(num_node);

        // construct SCC
        for node in 0..num_node {
            if state.index[node] == 0 {
                Scc::traverse(graph, &mut state, node);
            }
        }

        // collect all inter-group edges
        let num_group = state.nodes_in_group.len();
        let mut group_graph = vec![Vec::new(); num_group];
        for from in 0..num_node {
            for to in graph.next(from).into_iter() {
                let from_group = state.group_of_node[from];
                let to_group = state.group_of_node[to];
                if from_group != to_group {
                    group_graph[from_group].push(to_group);
                }
            }
        }

        // remove duplicated edges
        for group in 0..num_group {
            let edges = &mut group_graph[group];
            edges.sort();
            edges.dedup();
        }

        let SccConstructionState {
            group_of_node,
            nodes_in_group,
            ..
        } = state;

        Scc {
            graph,
            group_of_node,
            nodes_in_group,
            group_graph,
        }
    }

    // returns the lowest reachable node
    fn traverse(graph: &'a G, state: &mut SccConstructionState, node: usize) -> usize {
        state.assign_id(node);
        state.stack.push(node);

        let mut low_link = state.index[node];
        for next in graph.next(node).into_iter() {
            if state.index[next] == 0 {
                // not visited yet
                low_link = min(low_link, Scc::traverse(graph, state, next));
            } else if state.group_of_node[next] == 0 {
                // already in stack
                low_link = min(low_link, state.index[next]);
            }
        }

        // SCC boundary found
        if low_link == state.index[node] {
            // all nodes in the stack after this node belongs to the same group
            let mut new_group = Vec::new();
            let group_num = state.nodes_in_group.len() + 1;
            loop {
                let now = state.stack.pop().unwrap();
                state.group_of_node[now] = group_num;
                new_group.push(now);

                if now == node {
                    break;
                }
            }
            state.nodes_in_group.push(new_group);
        }

        low_link
    }

    fn topological_dfs(&self, state: &mut SccTopologicalOrderState, group: usize) {
        state.visited[group] = true;
        state.order.push(group);
        for &next_group in self.next_groups(group).iter() {
            if !state.visited[next_group] {
                self.topological_dfs(state, next_group)
            }
        }
    }

    pub fn topological_order(&self) -> Vec<usize> {
        let num_group = self.group_graph.len();
        let mut state = SccTopologicalOrderState::new(num_group);

        for group in 0..num_group {
            if !state.visited[group] {
                self.topological_dfs(&mut state, group);
            }
        }

        let mut result = state.order;
        result.reverse();
        result
    }

    pub fn graph(&self) -> &G {
        &self.graph
    }

    pub fn group_of_node(&self, idx: usize) -> usize {
        self.group_of_node[idx]
    }

    pub fn nodes_in_group(&self, idx: usize) -> &[usize] {
        &self.nodes_in_group[idx]
    }

    pub fn next_groups(&self, group_idx: usize) -> &[usize] {
        &self.group_graph[group_idx]
    }
}