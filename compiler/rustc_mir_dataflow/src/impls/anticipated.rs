// Partial Redundancy Elimination
#![allow(unused_imports)]
use std::collections::HashMap;

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
use rustc_serialize::{Decodable, Encodable};
use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_query_system::ich::StableHashingContext;
use rustc_macros::HashStable;



// use rustc_mir_dataflow::drop_flag_effects::on_all_inactive_variants;
use crate::{Analysis, AnalysisDomain, Backward, GenKill, GenKillAnalysis};

rustc_index::newtype_index! {
    #[derive(HashStable)]
    #[encodable]
    #[orderable]
    #[debug_format = "Expr{}"]
    pub struct ExprIdx {
        const EXPR_START = 0;
    }
}

#[derive(Hash)]
pub struct ExprSetElem {
    bin_op: BinOp,
    x: Local,
    y: Local,
}

pub struct ExprHashMap {
    table: HashMap<ExprSetElem, ExprIdx>,
}

impl ExprHashMap {

    fn new() -> ExprHashMap {
        return ExprHashMap { table: HashMap::new() }
    }

    fn expr_idx<'a>(&'a self, expr: &'a ExprSetElem) -> ExprIdx {
        if !self.table.contains(expr) {
            self.table.insert(expr, ExprIdx::new(self.table.len()))
        }
        return self.table[expr];
    }
}

pub struct AnticipatedExpressions {
    kill_ops: IndexVec<BasicBlock, BitSet<Local>>,
    expr_table: ExprHashMap,
}

impl AnticipatedExpressions {
    pub(super) fn transfer_function<'a, T>(&'a self, trans: &'a mut T, expr_table: &'a mut ExprHashMap) -> TransferFunction<'a, T> {
        TransferFunction { trans, kill_ops : self.kill_ops, expr_table : self.expr_table }
    }

    pub(super) fn new<'tcx>(body: &Body<'tcx>) -> AnticipatedExpressions {
        AnticipatedExpressions {
            kill_ops: IndexVec::from_elem(BitSet::new(), body.basic_blocks),
            expr_table: ExprHashMap::new()
        }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for AnticipatedExpressions {
    type Domain = BitSet<ExprIdx>;

    // domain for analysis is Local since i

    type Direction = Backward;
    const NAME: &'static str = "anticipated_expr";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        // bottom = nothing anticipated yet
        // TODO: update
        BitSet::new_empty(body.local_decls().len())
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {
        // should be set of all expressions; Not supported for backward analyses
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for AnticipatedExpressions {
    type Idx = ExprIdx;

    fn domain_size(&self, body: &Body<'tcx>) -> usize {
        // TODO: depends on how I see us doing stuff with the Idx
        body.local_decls().len()
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

        // self.transfer_function(trans).visit_terminator(terminator, location);
        // terminator.edges()
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
    kill_ops: &'a mut IndexVec<BasicBlock, BitSet<Local>>,
    expr_table: &'a mut ExprHashMap,
}

impl<'tcx, T> Visitor<'tcx> for TransferFunction<'_, T>
where
    T: GenKill<ExprIdx>,
{
    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {
        println!("stmt visited {:?}", stmt);

        if let StatementKind::Assign(box (place, rvalue)) = stmt.kind {

            // If current rvalue operands match no assigned operands in current BB, add to gen
            match rvalue {
                Rvalue::BinaryOp(bin_op, box (operand1, operand2))
                | Rvalue::CheckedBinaryOp(bin_op, box (operand1, operand2)) => {
                    // We need some way of dealing with constants
                    if let (Some(Place { local1, .. }), Some(Place { local2, .. })) = (operand1.place(), operand2.place()) {
                        if !self.kill_ops[location.block].contains(local1) && !self.kill_ops[location.block].contains(local2) {
                            println!("GEN expr {:?}", rvalue);
                            self.trans.gen(self.expr_table.expr_idx(ExprSetElem { bin_op, local1, local2 }));
                        }
                    }
                }
                Rvalue::Cast(..)
                | Rvalue::Ref(_, BorrowKind::Fake, _)
                | Rvalue::ShallowInitBox(..)
                | Rvalue::Use(..)
                | Rvalue::ThreadLocalRef(..)
                | Rvalue::Repeat(..)
                | Rvalue::Len(..)
                | Rvalue::NullaryOp(..)
                | Rvalue::UnaryOp(..)
                | Rvalue::Discriminant(..)
                | Rvalue::Aggregate(..)
                | Rvalue::CopyForDeref(..) => {}
            }
            
            // Any expressions in this BB that now contain this will need to be recalculated
            // And aren't anticipated anymore
            self.kill_ops[location.block].insert(place.local);

            // TODO: figure out how to actually kill stuff using kill_ops
            // Using GenKillAnalysis makes stuff trickier because it caches the state updates in its own function
            // Using Analysis directly, we could use statement_effect to get the input state for the current block and kill
            // inputs selectively.
        }
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

// #[allow(dead_code)]
// /// The set of locals that are borrowed at some point in the MIR body.
// pub fn anticipated_exprs(body: &Body<'_>) -> BitSet<Local> {
//     struct Anticipated(BitSet<Local>);

//     impl GenKill<Local> for Anticipated {
//         #[inline]
//         fn gen(&mut self, elem: Local) {
//             self.0.gen(elem)
//         }
//         #[inline]
//         fn kill(&mut self, _: Local) {
//             // Ignore borrow invalidation.
//         }
//     }

//     let mut anticipated = Anticipated(BitSet::new_empty(body.local_decls.len()));
//     TransferFunction { trans: &mut anticipated }.visit_body(body);
//     anticipated.0
// }