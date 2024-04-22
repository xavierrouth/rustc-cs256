// Partial Redundancy Elimination
#![allow(unused_imports)]

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::*;

use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    self, CallReturnPlaces, Local, Location, Place, StatementKind, TerminatorEdges,
};
use rustc_middle::ty::{self, Ty, TyCtxt};

use rustc_index::bit_set::{BitSet, ChunkedBitSet};
use rustc_index::{
    Idx, IndexVec
};
use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_macros::HashStable;

use std::fmt;

// use rustc_mir_dataflow::drop_flag_effects::on_all_inactive_variants;
use crate::{fmt::DebugWithContext, Analysis, AnalysisDomain, Backward, GenKill, GenKillAnalysis};

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

impl <A> DebugWithContext<A> for ExprIdx {
    fn fmt_with(&self, _ctxt: &A, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "hi")
        // write!(f, "{:?}", ctxt.location(*self))
    }
}

#[derive(Hash, Eq, PartialEq)]
pub struct ExprSetElem {
    bin_op: BinOp,
    local1: Local,
    local2: Local,
}


#[allow(rustc::default_hash_types)]
pub struct ExprHashMap {
    expr_table: HashMap<ExprSetElem, ExprIdx>,
    operand_table: HashMap<Local, HashSet<ExprIdx>>
}

impl ExprHashMap {

    /// We now parse the body to add a global operand -> expression mapping
    /// This now enables kill to do a lookup to add expressions to the kill set based on
    /// defs in the basic block
    fn parse_body(&mut self, body: &Body<'_>) -> &mut ExprHashMap {
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                
                // We only care about assignments for now
                if let StatementKind::Assign(box (_place, rvalue)) = &statement.kind {
        
                    // If current rvalue operands match no assigned operands in current BB, add to gen
                    match rvalue {
                        Rvalue::BinaryOp(bin_op, box (operand1, operand2))
                        | Rvalue::CheckedBinaryOp(bin_op, box (operand1, operand2)) => {
                            // We need some way of dealing with constants
                            if let (Some(Place { local: local1, .. }), Some(Place { local: local2, .. })) = (operand1.place(), operand2.place()) {
                                let expr_idx = self.expr_idx(
                                    ExprSetElem { bin_op: *bin_op, local1, local2 });
                                
                                // Map operands to expressions
                                if let Some(local1_exprs) = self.operand_table.get_mut(&local1) {
                                    local1_exprs.insert(expr_idx);
                                }
                                else {
                                    #[allow(rustc::default_hash_types)]
                                    self.operand_table.insert(local1, HashSet::from([expr_idx]));
                                }
                                if let Some(local2_exprs) = self.operand_table.get_mut(&local2) {
                                    local2_exprs.insert(expr_idx);
                                }
                                else {
                                    #[allow(rustc::default_hash_types)]
                                    self.operand_table.insert(local2, HashSet::from([expr_idx]));
                                }
                            }
                        }
                        
                        _ => {}
                    }
                }
            }
        }
        self
    }

    #[allow(dead_code)]
    fn new(body: &Body<'_>) -> ExprHashMap {
        #[allow(rustc::default_hash_types)]
        let mut _self = ExprHashMap { expr_table: HashMap::new(), operand_table: HashMap::new() };
        // Iterate through exprs and add all expressions to table
        _self.parse_body(body);
        _self
    }

    fn expr_idx(&mut self, expr: ExprSetElem) -> ExprIdx {
        let len = self.expr_table.len();
        self.expr_table.entry(expr).or_insert(ExprIdx::new(len)).clone()
    }
}

pub struct AnticipatedExpressions {
    kill_ops: IndexVec<BasicBlock, BitSet<Local>>,
    expr_table: ExprHashMap,
    bitset_size: usize,
}

impl AnticipatedExpressions {
    // Can we return this? 
    pub(super) fn transfer_function<'a, T>(&'a mut self, trans: &'a mut T) -> TransferFunction<'a, T> {
        TransferFunction { 
            trans, 
            kill_ops: &mut self.kill_ops, 
            expr_table: &mut self.expr_table }
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
        let size = Self::count_statements(body);
        let _self = AnticipatedExpressions {
            kill_ops: IndexVec::from_elem(BitSet::new_empty(size), &body.basic_blocks), // FIXME: This size '100'
            expr_table: ExprHashMap::new(body),
            bitset_size: size
        };
        
        _self
    }
}

impl<'tcx> AnalysisDomain<'tcx> for AnticipatedExpressions {
    type Domain = BitSet<ExprIdx>;

    // domain for analysis is Local since i

    type Direction = Backward;
    const NAME: &'static str = "anticipated_expr";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        // bottom = nothing anticipated yet
        // TODO: update
        // let len = body.local_decls().len()
        // Should size be local_decls.len() or count of all statements?
        BitSet::new_empty(self.bitset_size)
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
    kill_ops: &'a mut IndexVec<BasicBlock, BitSet<Local>>, // List of defs within a BB, if we have an expression in a BB that has a killed op from the same BB in 
    expr_table: &'a mut ExprHashMap,
}

impl<'tcx, T> Visitor<'tcx> for TransferFunction<'_, T>
where
    T: GenKill<ExprIdx>,
{
    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {
        println!("stmt visited {:?}", stmt);

        // We only care about assignments for now
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {

            // If current rvalue operands match no assigned operands in current BB, add to gen
            match rvalue {
                Rvalue::BinaryOp(bin_op, box (operand1, operand2))
                | Rvalue::CheckedBinaryOp(bin_op, box (operand1, operand2)) => {
                    // We need some way of dealing with constants
                    if let (Some(Place { local: local1, .. }), Some(Place { local: local2, .. })) = (operand1.place(), operand2.place()) {
                        if !self.kill_ops[location.block].contains(local1) && !self.kill_ops[location.block].contains(local2) {
                            println!("GEN expr {:?}", rvalue.clone());
                            self.trans.gen(self.expr_table.expr_idx(
                                ExprSetElem { bin_op: *bin_op, local1, local2 }));
                        }
                    }
                }
                
                _ => {}
            }
            
            // Any expressions in this BB that now contain this will need to be recalculated
            // And aren't anticipated anymore
            self.kill_ops[location.block].insert(place.local);

            // We consider any assignments to be defs, and so we add all expressions that
            // use that def'd operand to kill
            // We do this using the previously calculated operand -> exprs mapping in the expr_table
            if let Some(exprs) = self.expr_table.operand_table.get(&place.local) {
                #[allow(rustc::potential_query_instability)]
                for expr_id in exprs.iter() {
                    self.trans.kill(*expr_id);
                }
            }
        }
    }
}
