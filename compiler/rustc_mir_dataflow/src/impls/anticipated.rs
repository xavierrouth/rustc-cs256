// Partial Redundancy Elimination
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
    fmt::DebugWithContext, lattice::Dual, Analysis, AnalysisDomain, Backward,
    Forward, GenKill, GenKillAnalysis, JoinSemiLattice,
};

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

#[derive(Hash, Eq, PartialEq, Debug)]
pub struct ExprSetElem {
    pub bin_op: BinOp,
    pub local1: Local,
    pub local2: Local,
}

#[allow(rustc::default_hash_types)]
pub struct ExprHashMap {
    pub expr_table: HashMap<ExprSetElem, ExprIdx>,
    pub operand_table: HashMap<Local, HashSet<ExprIdx>>,
}

#[allow(rustc::default_hash_types)]
impl ExprHashMap {
    /// We now parse the body to add a global operand -> expression mapping
    /// This now enables kill to do a lookup to add expressions to the kill set based on
    /// defs in the basic block
    
    #[allow(dead_code)]
    pub fn new() -> ExprHashMap {
        ExprHashMap { expr_table: HashMap::new(), operand_table: HashMap::new() }
    }

    pub fn expr_idx(&mut self, expr: ExprSetElem) -> ExprIdx {
        let len = self.expr_table.len();
        self.expr_table.entry(expr).or_insert(ExprIdx::new(len)).clone()
    }

    pub fn get_operand_mapping(&mut self, op: Local) -> Option<&HashSet<ExprIdx>> {
        self.operand_table.get(&op)
    }

    pub fn add_operand_mapping(&mut self, op: Local, expr: ExprIdx) -> bool {
        self.operand_table.entry(op).or_insert(HashSet::new()).insert(expr)
    }
}

pub struct AnticipatedExpressions {
    expr_table: ExprHashMap,
    pub bitset_size: usize,
}

impl AnticipatedExpressions {
    // Can we return this?
    pub fn fmt_domain(
        &self,
        domain: &<AnticipatedExpressions as AnalysisDomain<'_>>::Domain,
    ) -> () {
        let bitset: &Dual<BitSet<ExprIdx>> = domain;

        #[allow(rustc::potential_query_instability)]
        for (key, val) in self.expr_table.expr_table.iter() {
            println!("{:?}, {:?}", key, val);
        }
        println!("{:?}", bitset);
        // let idx: ExprIdx = domain.
    }

    pub(super) fn transfer_function<'a, T>(
        &'a mut self,
        trans: &'a mut T,
    ) -> TransferFunction<'a, T> {
        TransferFunction { trans, expr_table: &mut self.expr_table }
    }

    fn count_statements(body: &Body<'_>) -> usize {
        let mut statement_count = 0;
        for block in body.basic_blocks.iter() {
            for _statement in &block.statements {
                // Count only statements, not terminators
                //if !matches!(statement.kind, StatementKind::Terminator(_)) {
                statement_count += 1;
                //}
            }
        }
        statement_count
    }

    #[allow(dead_code)]
    pub fn new<'tcx>(body: &Body<'tcx>) -> AnticipatedExpressions {
        let size = Self::count_statements(body) + body.local_decls.len();

        println!("size: {size}");
        AnticipatedExpressions {
            expr_table: ExprHashMap::new(),
            bitset_size: size,
        }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for AnticipatedExpressions {
    type Domain = Dual<BitSet<ExprIdx>>;

    // domain for analysis is Local since i
    type Direction = Backward;
    const NAME: &'static str = "anticipated_expr";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        // bottom = nothing anticipated yet
        // TODO: update
        // let len = body.local_decls().len()
        // Should size be local_decls.len() or count of all statements?
        Dual(BitSet::new_filled(self.bitset_size))
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {
        // should be set of all expressions; Not supported for backward analyses
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for AnticipatedExpressions {
    type Idx = ExprIdx;

    fn domain_size(&self, _body: &Body<'tcx>) -> usize {
        // TODO: depends on how I see us doing stuff with the Idx
        // body.local_decls().len()
        self.bitset_size
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.transfer_function(trans).visit_statement(statement, location);
    }

    fn terminator_effect<'mir>(
        &mut self,
        _trans: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        _location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        // TODO: We probably have to do something with SwitchInt or one of them, but I believe the engine
        // considers that with merges, though I need to look back again
        // For now, ignoring

        // self.transfer_function(trans).visit_terminator(terminator, location);
        // terminator.edges()
        //TerminatorEdges::default()

        // Clear all elements if the terminator has no outgoing edges
        if let TerminatorEdges::None = terminator.edges() {
            _trans.0.clear();
        }
        terminator.edges()
    }

    fn call_return_effect(
        &mut self,
        _trans: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}

/// A `Visitor` that defines the transfer function for `AnticipatedExpressions`.
pub(super) struct TransferFunction<'a, T> {
    trans: &'a mut T,
    // kill_ops: &'a mut IndexVec<BasicBlock, FxHashMap<Local, usize>>, // List of defs within a BB, if we have an expression in a BB that has a killed op from the same BB in
    expr_table: &'a mut ExprHashMap,
}

impl<'tcx, T> Visitor<'tcx> for TransferFunction<'_, T>
where
    T: GenKill<ExprIdx>,
{
    fn visit_body(&mut self, body: &Body<'tcx>) {
        println!("visit body: {:?}", body);
    }

    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &BasicBlockData<'tcx>) {
        println!("visit block: {:?} {:?}", block, data);
    }

    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {
        println!("{:?}: stmt visited {:?}", location, stmt);

        // We only care about assignments for now
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            // If current rvalue operands match no assigned operands in current BB, add to gen
            match rvalue {
                Rvalue::BinaryOp(bin_op, box (operand1, operand2))
                | Rvalue::CheckedBinaryOp(bin_op, box (operand1, operand2)) => {
                    // We need some way of dealing with constants
                    if let (Some(Place { local: local1, .. }), Some(Place { local: local2, .. })) =
                        (operand1.place(), operand2.place())
                    {
                        // Add expressions as we encounter them to the GEN set
                        // Expressions that have re-defined args within the basic block will naturally be killed
                        // as those defs are reached
                        println!("GEN expr {:?}", rvalue.clone());
                        let expr_idx = self.expr_table.expr_idx(ExprSetElem {
                            bin_op: *bin_op,
                            local1,
                            local2,
                        });
                        self.trans.gen(expr_idx);

                        // Add to the expr_set
                        self.expr_table.add_operand_mapping(local1, expr_idx);
                        self.expr_table.add_operand_mapping(local2, expr_idx);
                    }
                }

                _ => {}
            }

            // We consider any assignments to be defs, and so we add all expressions that
            // use that def'd operand to kill
            // We do this using the previously calculated operand -> exprs mapping in the expr_table
            if let Some(exprs) = self.expr_table.get_operand_mapping(place.local) {
                #[allow(rustc::potential_query_instability)]
                for expr_id in exprs.iter() {
                    println!("KILL expr {:?}", expr_id);
                    self.trans.kill(*expr_id);
                }
            }
        }
    }
}
