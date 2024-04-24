// Partial Redundancy Elimination
#![allow(unused_imports)]

use std::collections::HashMap;

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
use crate::framework::BitSetExt;
use crate::Forward;

// use rustc_mir_dataflow::drop_flag_effects::on_all_inactive_variants;
use crate::{fmt::DebugWithContext, Analysis, AnalysisDomain, Backward, GenKill, GenKillAnalysis};

use crate::impls::anticipated::{ExprHashMap, ExprIdx};
use crate::impls::AnticipatedExpressions;
use crate::lattice::Dual;

use crate::Results;
use crate::ResultsCursor;
use crate::impls::anticipated::ExprSetElem;

type AnticipatedExpressionsResults<'mir, 'tcx> = ResultsCursor<'mir, 'tcx, AnticipatedExpressions>;
type AvailableExpressionsResults<'mir, 'tcx> = ResultsCursor<'mir, 'tcx, AvailableExpressions>;


pub struct PostponableExpressions<'tcx> {
    //anticipated_exprs: AnticipatedExpressionsResults<'mir, 'tcx>,
    //available_exprs: AvailableExpressionsResults<'mir, 'tcx>,
    earliest_exprs: IndexVec<BasicBlock, <PostponableExpressions<'tcx> as AnalysisDomain<'tcx>>::Domain>,
    expr_table: ExprHashMap,
    bitset_size: usize,
}


impl<'mir, 'tcx> PostponableExpressions<'tcx> {

    // Can we return this?
    pub(super) fn transfer_function<'a, T>(
        &'a mut self,
        trans: &'a mut T,
    ) -> PostTransferFunction<'a, 'mir, 'tcx, T> {
        PostTransferFunction {
            earliest_exprs: &mut self.earliest_exprs,
            trans,
            expr_table: &mut self.expr_table,
        }
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
    pub fn new(
        body: &Body<'tcx>,
        anticipated_exprs: AnticipatedExpressionsResults<'mir, 'tcx>,
        available_exprs: AvailableExpressionsResults<'mir, 'tcx>,
    ) -> PostponableExpressions<'mir, 'tcx> {
        let size = Self::count_statements(body) + body.local_decls.len();
        assert!(size == anticipated_exprs.results().analysis.bitset_size);

        let set_diff = |i: BasicBlock| -> <PostponableExpressions as AnalysisDomain<'_>>::Domain {
            let anticpated = anticipated_exprs.results().entry_set_for_block(i);
            let available = available_exprs.results().entry_set_for_block(i);
            anticpated.subtract(available)
        };
        
        let earliest_exprs = IndexVec::from_fn_n(set_diff, body.basic_blocks.len());


        PostponableExpressions {
            earliest_exprs: earliest_exprs,
            // kill_ops: IndexVec::from_elem(BitSet::new_empty(size), &body.basic_blocks), // FIXME: This size '100'
            expr_table: ExprHashMap::new(),
            bitset_size: size,
        }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for PostponableExpressions<'_, '_> {
    type Domain = Dual<BitSet<ExprIdx>>;
    type Direction = Forward;

    // domain for analysis is Local since i

    const NAME: &'static str = "postponable_expr";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        // bottom = nothing Postponable yet
        // TODO: update
        // let len = body.local_decls().len()
        // Should size be local_decls.len() or count of all statements?
        Dual(BitSet::new_filled(self.bitset_size))
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, domain: &mut Self::Domain) {
        // should be set of all expressions; Not supported for backward analyses
        domain.0.clear();
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for PostponableExpressions<'_, 'tcx> {
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
        trans: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        // TODO: We probably have to do something with SwitchInt or one of them, but I believe the engine
        // considers that with merges, though I need to look back again
        // For now, ignoring

        self.transfer_function(trans).visit_terminator(terminator, location);

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

// A `Visitor` that defines the transfer function for `PostponableExpressions`.
// 
#[allow(dead_code)]
pub(super) struct PostTransferFunction<'a, 'tcx, T> {
    trans: &'a mut T,
    earliest_exprs: &'a IndexVec<BasicBlock, <PostponableExpressions<'tcx> as AnalysisDomain<'tcx>>::Domain>,
    //kill_ops: &'a mut IndexVec<BasicBlock, BitSet<Local>>, // List of defs within a BB, if we have an expression in a BB that has a killed op from the same BB in
    expr_table: &'a mut ExprHashMap,
}

// Join needs to be intersect..., so domain should probably have Dual
impl<'a, 'mir, 'tcx, T> Visitor<'tcx> for PostTransferFunction<'a, 'tcx, T>
where
    T: GenKill<ExprIdx>,
{
    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {

        self.super_statement(stmt, location);
        println!("stmt visited {:?}", stmt);
    }

    fn visit_terminator (& mut self, terminator: & mir::Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location); // What??
        // println!( "visit terminator {:?}", terminator);
        
        // For each expression that is anticipated in this block, mark it as Postponable.


        /* Kill All expressions that have been assigned to are in the expression table */
        // FIXME: How do we only kill expressions that are assigned to after the expression is gen'd
    }

}