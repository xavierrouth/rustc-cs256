#![allow(unused_imports)]

use std::collections::{HashMap, HashSet};

use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::graph::{WithStartNode, WithSuccessors};
use rustc_data_structures::sync::HashMapExt;
use rustc_middle::mir::*;

use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    self, CallReturnPlaces, Local, Location, Place, StatementKind, TerminatorEdges,
};
use rustc_middle::ty::{self, Ty, TyCtxt};

use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_index::bit_set::{BitSet, ChunkedBitSet};
use rustc_index::{Idx, IndexVec};
use rustc_macros::HashStable;

use std::fmt;

// use rustc_mir_dataflow::drop_flag_effects::on_all_inactive_variants;
use crate::{
    fmt::DebugWithContext, lattice::Dual, Analysis, AnalysisDomain, Backward, Forward, GenKill,
    GenKillAnalysis, JoinSemiLattice,
};

#[derive(Hash, Eq, PartialEq, Debug, Clone)]
pub struct ExprSetElem {
    pub bin_op: BinOp,
    pub local1: Local,
    pub local2: Local,
}

#[allow(rustc::default_hash_types)]
#[derive(Clone)]
pub struct ExprHashMap {
    pub expr_table: HashMap<ExprSetElem, ExprIdx>,
    pub bb_expr_map: HashMap<BasicBlock, HashSet<ExprIdx>>,
    pub operand_table: HashMap<Local, HashSet<ExprIdx>>,
    pub terminal_blocks: HashSet<BasicBlock>,
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "Expr({})"]
    pub struct ExprIdx {
        const EXPR_START = 0;
    }
}

/*
impl DebugWithContext<Borrows<'_, '_>> for BorrowIndex {
    fn fmt_with(&self, ctxt: &Borrows<'_, '_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", ctxt.location(*self))
    }
}*/

impl<A> DebugWithContext<A> for ExprIdx {
    fn fmt_with(&self, _ctxt: &A, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // ctxt.
        write!(f, "{:?}", self)
        // write!(f, "{:?}", ctxt.location(*self))
    }
}

#[allow(rustc::default_hash_types)]
impl ExprHashMap {
    /// We now parse the body to add a global operand -> expression mapping
    /// This now enables kill to do a lookup to add expressions to the kill set based on
    /// defs in the basic block

    #[allow(dead_code)]
    pub fn new() -> ExprHashMap {
        ExprHashMap {
            expr_table: HashMap::new(),
            bb_expr_map: HashMap::new(),
            operand_table: HashMap::new(),
            terminal_blocks: HashSet::new(),
        }
    }

    pub fn expr_idx(&self, expr: ExprSetElem) -> Option<ExprIdx> {
        self.expr_table.get(&expr).clone().copied()
    }

    pub fn expr_idx_mut(&mut self, expr: ExprSetElem) -> ExprIdx {
        let len = self.expr_table.len();
        self.expr_table.entry(expr).or_insert(ExprIdx::new(len)).clone()
    }

    pub fn get_operand_mapping(&self, op: Local) -> Option<&HashSet<ExprIdx>> {
        self.operand_table.get(&op)
    }

    pub fn add_operand_mapping(&mut self, op: Local, expr: ExprIdx) -> bool {
        self.operand_table.entry(op).or_insert(HashSet::new()).insert(expr)
    }
}
