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

pub struct AvailableExpressions<'mir, 'tcx> {
    anticipated_exprs: AnticipatedExpressionsResults<'mir, 'tcx>,
    // kill_ops: IndexVec<BasicBlock, BitSet<Local>>,
    expr_table: ExprHashMap,
    bitset_size: usize,
}


impl<'mir, 'tcx> AvailableExpressions<'mir, 'tcx> {

    pub fn fmt_domain(
        &self,
        domain: &<AnticipatedExpressions as AnalysisDomain<'_>>::Domain,
    ) -> () {
        let bitset = domain;

        #[allow(rustc::potential_query_instability)]
        for (key, val) in self.expr_table.expr_table.iter() {
            println!("{:?}, {:?}", key, val);
        }
        println!("{:?}", bitset);
        // let idx: ExprIdx = domain.
    }

    // Can we return this?
    pub(super) fn transfer_function<'a, T>(
        &'a mut self,
        trans: &'a mut T,
    ) -> AvailTransferFunction<'a, 'mir, 'tcx, T> {
        AvailTransferFunction {
            anticipated_exprs: &mut self.anticipated_exprs,
            trans,
            // kill_ops: &mut self.kill_ops,
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
    ) -> AvailableExpressions<'mir, 'tcx> {
        let size = Self::count_statements(body) + body.local_decls.len();
        assert!(size == anticipated_exprs.results().analysis.bitset_size);

        AvailableExpressions {
            anticipated_exprs: anticipated_exprs,
            // kill_ops: IndexVec::from_elem(BitSet::new_empty(size), &body.basic_blocks), // FIXME: This size '100'
            expr_table: ExprHashMap::new(),
            bitset_size: size,
        }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for AvailableExpressions<'_, '_> {
    type Domain = Dual<BitSet<ExprIdx>>;
    type Direction = Forward;

    // domain for analysis is Local since i

    const NAME: &'static str = "available_expr";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        // bottom = nothing Available yet
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

impl<'tcx> GenKillAnalysis<'tcx> for AvailableExpressions<'_, 'tcx> {
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
        // terminator.edges()
        // TerminatorEdges::default()
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

// A `Visitor` that defines the transfer function for `AvailableExpressions`.
// 
#[allow(dead_code)]
pub(super) struct AvailTransferFunction<'a, 'mir, 'tcx, T> {
    anticipated_exprs: &'a mut AnticipatedExpressionsResults<'mir, 'tcx>,
    trans: &'a mut T,
    //kill_ops: &'a mut IndexVec<BasicBlock, BitSet<Local>>, // List of defs within a BB, if we have an expression in a BB that has a killed op from the same BB in
    expr_table: &'a mut ExprHashMap,
}

// Join needs to be intersect..., so domain should probably have Dual
impl<'a, 'mir, 'tcx, T> Visitor<'tcx> for AvailTransferFunction<'a, 'mir, 'tcx, T>
where
    T: GenKill<ExprIdx>,
{
    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {

        if location.statement_index == 0 {
            println!("Entering BB: {:?}", location.block);

            let anticipated_exprs = self.anticipated_exprs.results().entry_set_for_block(location.block);
            
            for _expr in anticipated_exprs.0.iter() {
                //println!("adding anticipated expr: {:?}", expr);
                // self.trans.gen(expr);
            }
        }

        self.super_statement(stmt, location);
        println!("stmt visited {:?}", stmt);

        // For an assignment place = rvalue
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
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

                        // Add a mapping from these operands to this expression.
                        self.expr_table.add_operand_mapping(local1, expr_idx);
                        self.expr_table.add_operand_mapping(local2, expr_idx);
                    }
                }
                _ => {}
            }
            
            // Kill any expressions that have their operands reassigned here.

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

    fn visit_terminator (& mut self, terminator: & mir::Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location); // What??
        // println!( "visit terminator {:?}", terminator);
        
        // For each expression that is anticipated in this block, mark it as available.


        /* Kill All expressions that have been assigned to are in the expression table */
        // FIXME: How do we only kill expressions that are assigned to after the expression is gen'd
    }

    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &BasicBlockData<'tcx>) {
        println!(
            "anticipated exprs for current BB {:?}",
            self.anticipated_exprs.seek_to_block_start(block)
        );
        println!("BB data {:?}", data);
    }

    // fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
    //     self.super_rvalue(rvalue, location);

    //     match rvalue {
    //         // We ignore fake borrows as these get removed after analysis and shouldn't effect
    //         // the layout of generators.
    //         Rvalue::AddressOf(_, borrowed_place)
    //         | Rvalue::Ref(_, BorrowKind::Mut { .. } | BorrowKind::Shared, borrowed_place) => {
    //             if !borrowed_place.is_indirect() {
    //                 println!("rvalue {:?}", rvalue);
    //                 println!("stmt place {:?}", borrowed_place);

    //                 self.trans.gen(borrowed_place.local);
    //             }
    //         }

    //         Rvalue::BinaryOp(_, operands) => {
    //             println!("operand 1: {:?}\n", operands.0);
    //             println!("operand 2: {:?}\n", operands.1);
    //             println!("place of operand 1: {:?}\n", operands.0.place());
    //             println!("place of operand 2: {:?}\n", operands.1.place());
    //             if !operands.0.place().is_none() && !operands.1.place().is_none() {
    //                 let op_1 = operands.0.place().unwrap();
    //                 let op_2 = operands.1.place().unwrap();
    //                 println!("local associated with op 1 {:?}", op_1.local);
    //                 println!("local associated with op 2 {:?}", op_2.local);
    //                 println!("bb at location {:?}\n", location.block);
    //                 // use external function to lookup data for bb

    //                 /* for statement in basic_blocks[location.block].statements {
    //                     match statement.kind {
    //                         StatementKind::Assign(assign_pair) => {
    //                             if assign_pair.0 == op_1 {
    //                                 println!("FOUND A MATCH for OP 1\n");
    //                             }
    //                             if assign_pair.0 == op_2 {
    //                                 println!("FOUND A MATCH for OP 2\n");
    //                             }
    //                         }
    //                         _ => {}
    //                     }
    //                 } */
    //                 // self.trans.gen(operands.0.place().unwrap().local);
    //             }
    //         }

    //         Rvalue::Cast(..)
    //         | Rvalue::Ref(_, BorrowKind::Fake, _)
    //         | Rvalue::ShallowInitBox(..)
    //         | Rvalue::Use(..)
    //         | Rvalue::ThreadLocalRef(..)
    //         | Rvalue::Repeat(..)
    //         | Rvalue::Len(..)
    //         | Rvalue::CheckedBinaryOp(..)
    //         | Rvalue::NullaryOp(..)
    //         | Rvalue::UnaryOp(..)
    //         | Rvalue::Discriminant(..)
    //         | Rvalue::Aggregate(..)
    //         | Rvalue::CopyForDeref(..) => {}
    //     }
    // }

    // fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
    //     self.super_terminator(terminator, location);

    //     match terminator.kind {
    //         TerminatorKind::Drop { place: dropped_place, .. } => {
    //             // Drop terminators may call custom drop glue (`Drop::drop`), which takes `&mut
    //             // self` as a parameter. In the general case, a drop impl could launder that
    //             // reference into the surrounding environment through a raw pointer, thus creating
    //             // a valid `*mut` pointing to the dropped local. We are not yet willing to declare
    //             // this particular case UB, so we must treat all dropped locals as mutably borrowed
    //             // for now. See discussion on [#61069].
    //             //
    //             // [#61069]: https://github.com/rust-lang/rust/pull/61069
    //             if !dropped_place.is_indirect() {
    //                 self.trans.gen(dropped_place.local);
    //             }
    //         }

    //         TerminatorKind::UnwindTerminate(_)
    //         | TerminatorKind::Assert { .. }
    //         | TerminatorKind::Call { .. }
    //         | TerminatorKind::FalseEdge { .. }
    //         | TerminatorKind::FalseUnwind { .. }
    //         | TerminatorKind::CoroutineDrop
    //         | TerminatorKind::Goto { .. }
    //         | TerminatorKind::InlineAsm { .. }
    //         | TerminatorKind::UnwindResume
    //         | TerminatorKind::Return
    //         | TerminatorKind::SwitchInt { .. }
    //         | TerminatorKind::Unreachable
    //         | TerminatorKind::Yield { .. } => {}
    //     }
    // }
}