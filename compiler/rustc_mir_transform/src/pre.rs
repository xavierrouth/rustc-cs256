// Partial Redundancy Elimination
#![allow(unused_imports)]
use rustc_middle::mir::*;

use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{
    self, CallReturnPlaces, Local, Location, Place, StatementKind, TerminatorEdges,
};
use rustc_middle::ty::{self, Ty, TyCtxt};

use rustc_index::bit_set::{BitSet, ChunkedBitSet};
use rustc_index::Idx;

// use rustc_mir_dataflow::drop_flag_effects::on_all_inactive_variants;
use rustc_mir_dataflow::drop_flag_effects_for_function_entry;
use rustc_mir_dataflow::drop_flag_effects_for_location;
use rustc_mir_dataflow::elaborate_drops::DropFlagState;
use rustc_mir_dataflow::move_paths::{
    HasMoveData, InitIndex, InitKind, LookupResult, MoveData, MovePathIndex,
};
use rustc_mir_dataflow::on_lookup_result_bits;
use rustc_mir_dataflow::MoveDataParamEnv;
use rustc_mir_dataflow::SwitchIntEdgeEffects;
use rustc_mir_dataflow::{drop_flag_effects, on_all_children_bits};
use rustc_mir_dataflow::{
    lattice, Analysis, AnalysisDomain, Backward, GenKill, GenKillAnalysis, MaybeReachable,
};

#[allow(dead_code)]
pub struct PartialRedundancyElimination;

#[allow(unused_variables)]
impl<'tcx> MirPass<'tcx> for PartialRedundancyElimination {
    fn is_enabled(&self, _sess: &rustc_session::Session) -> bool {
        false
    }
    
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        println!("Running PartialRedundancyElimination on {:?}", body.source);
        // println!("body anticipated exprs {:?}", anticipated_exprs(&body));
        for data in body.basic_blocks.as_mut_preserves_cfg() {
            data.statements.retain(|statement| {
                println!("PRE statement {:?}", statement);
                true
            })
        }
        for block in body.basic_blocks_mut() {
            let mut locals_vec: Vec<Local> = vec![];

            for statement in block.statements.iter_mut() {
                match statement.kind {
                    StatementKind::Assign(box (place, ref mut rvalue)) => {
                        locals_vec.push(place.local);
                        match rvalue {
                            // We ignore fake borrows as these get removed after analysis and shouldn't effect
                            // the layout of generators.
                            Rvalue::AddressOf(_, borrowed_place)
                            | Rvalue::Ref(
                                _,
                                BorrowKind::Mut { .. } | BorrowKind::Shared,
                                borrowed_place,
                            ) => {
                                if !borrowed_place.is_indirect() {
                                    // println!("rvalue {:?}", &rvalue);
                                    // println!("stmt place {:?}", borrowed_place);

                                    // self.trans.gen(borrowed_place.local);
                                }
                            }

                            Rvalue::BinaryOp(_, operands) => {
                                println!("operand 1: {:?}\n", operands.0);
                                println!("operand 2: {:?}\n", operands.1);
                                println!("place of operand 1: {:?}\n", operands.0.place());
                                println!("place of operand 2: {:?}\n", operands.1.place());
                                if !operands.0.place().is_none() && !operands.1.place().is_none() {
                                    let op_1 = operands.0.place().unwrap();
                                    let op_2 = operands.1.place().unwrap();
                                    println!("local associated with op 1 {:?}", op_1.local);
                                    println!("local associated with op 2 {:?}", op_2.local);
                                    if locals_vec.contains(&op_1.local)
                                        || locals_vec.contains(&op_2.local)
                                    {
                                        println!("KILL");
                                    } else {
                                        println!("GEN");
                                    }
                                    // use external function to lookup data for bb

                                    /* for statement in basic_blocks[location.block].statements {
                                        match statement.kind {
                                            StatementKind::Assign(assign_pair) => {
                                                if assign_pair.0 == op_1 {
                                                    println!("FOUND A MATCH for OP 1\n");
                                                }
                                                if assign_pair.0 == op_2 {
                                                    println!("FOUND A MATCH for OP 2\n");
                                                }
                                            }
                                            _ => {}
                                        }
                                    } */
                                    // self.trans.gen(operands.0.place().unwrap().local);
                                }
                            }

                            Rvalue::Cast(..)
                            | Rvalue::Ref(_, BorrowKind::Fake, _)
                            | Rvalue::ShallowInitBox(..)
                            | Rvalue::Use(..)
                            | Rvalue::ThreadLocalRef(..)
                            | Rvalue::Repeat(..)
                            | Rvalue::Len(..)
                            | Rvalue::CheckedBinaryOp(..)
                            | Rvalue::NullaryOp(..)
                            | Rvalue::UnaryOp(..)
                            | Rvalue::Discriminant(..)
                            | Rvalue::Aggregate(..)
                            | Rvalue::CopyForDeref(..) => {}
                        }
                    }
                    _ => {}
                }
            }
            locals_vec.clear();
        }
    }
}

pub struct AnticipatedExpressions;

impl AnticipatedExpressions {
    pub(super) fn transfer_function<'a, T>(&'a self, trans: &'a mut T) -> TransferFunction<'a, T> {
        TransferFunction { trans }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for AnticipatedExpressions {
    type Domain = BitSet<Local>;

    // domain for analysis is Local since i

    type Direction = Backward;
    const NAME: &'static str = "anticipated_expr";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        // bottom = nothing anticipated yet
        BitSet::new_empty(body.local_decls().len())
    }

    fn initialize_start_block(&self, _: &Body<'tcx>, _: &mut Self::Domain) {
        // should be set of all expressions; Not supported for backward analyses
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for AnticipatedExpressions {
    type Idx = Local;

    fn domain_size(&self, body: &Body<'tcx>) -> usize {
        body.local_decls.len()
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

/// A `Visitor` that defines the transfer function for `AnticipatedExpressions`.
pub(super) struct TransferFunction<'a, T> {
    trans: &'a mut T,
}

impl<'tcx, T> Visitor<'tcx> for TransferFunction<'_, T>
where
    T: GenKill<Local>,
{
    fn visit_statement(&mut self, stmt: &Statement<'tcx>, location: Location) {
        println!("stmt visited {:?}", stmt);

        self.super_statement(stmt, location);

        // When we reach a `StorageDead` statement, we can assume that any pointers to this memory
        // are now invalid.

        if let StatementKind::StorageDead(local) = stmt.kind {
            println!("killed stmt {:?}", stmt);
            self.trans.kill(local);
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);

        match rvalue {
            // We ignore fake borrows as these get removed after analysis and shouldn't effect
            // the layout of generators.
            Rvalue::AddressOf(_, borrowed_place)
            | Rvalue::Ref(_, BorrowKind::Mut { .. } | BorrowKind::Shared, borrowed_place) => {
                if !borrowed_place.is_indirect() {
                    println!("rvalue {:?}", rvalue);
                    println!("stmt place {:?}", borrowed_place);

                    self.trans.gen(borrowed_place.local);
                }
            }

            Rvalue::BinaryOp(_, operands) => {
                println!("operand 1: {:?}\n", operands.0);
                println!("operand 2: {:?}\n", operands.1);
                println!("place of operand 1: {:?}\n", operands.0.place());
                println!("place of operand 2: {:?}\n", operands.1.place());
                if !operands.0.place().is_none() && !operands.1.place().is_none() {
                    let op_1 = operands.0.place().unwrap();
                    let op_2 = operands.1.place().unwrap();
                    println!("local associated with op 1 {:?}", op_1.local);
                    println!("local associated with op 2 {:?}", op_2.local);
                    println!("bb at location {:?}\n", location.block);
                    // use external function to lookup data for bb

                    /* for statement in basic_blocks[location.block].statements {
                        match statement.kind {
                            StatementKind::Assign(assign_pair) => {
                                if assign_pair.0 == op_1 {
                                    println!("FOUND A MATCH for OP 1\n");
                                }
                                if assign_pair.0 == op_2 {
                                    println!("FOUND A MATCH for OP 2\n");
                                }
                            }
                            _ => {}
                        }
                    } */
                    // self.trans.gen(operands.0.place().unwrap().local);
                }
            }

            Rvalue::Cast(..)
            | Rvalue::Ref(_, BorrowKind::Fake, _)
            | Rvalue::ShallowInitBox(..)
            | Rvalue::Use(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::Repeat(..)
            | Rvalue::Len(..)
            | Rvalue::CheckedBinaryOp(..)
            | Rvalue::NullaryOp(..)
            | Rvalue::UnaryOp(..)
            | Rvalue::Discriminant(..)
            | Rvalue::Aggregate(..)
            | Rvalue::CopyForDeref(..) => {}
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);

        match terminator.kind {
            TerminatorKind::Drop { place: dropped_place, .. } => {
                // Drop terminators may call custom drop glue (`Drop::drop`), which takes `&mut
                // self` as a parameter. In the general case, a drop impl could launder that
                // reference into the surrounding environment through a raw pointer, thus creating
                // a valid `*mut` pointing to the dropped local. We are not yet willing to declare
                // this particular case UB, so we must treat all dropped locals as mutably borrowed
                // for now. See discussion on [#61069].
                //
                // [#61069]: https://github.com/rust-lang/rust/pull/61069
                if !dropped_place.is_indirect() {
                    self.trans.gen(dropped_place.local);
                }
            }

            TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Assert { .. }
            | TerminatorKind::Call { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::Goto { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::Return
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Unreachable
            | TerminatorKind::Yield { .. } => {}
        }
    }
}

#[allow(dead_code)]
/// The set of locals that are borrowed at some point in the MIR body.
pub fn anticipated_exprs(body: &Body<'_>) -> BitSet<Local> {
    struct Anticipated(BitSet<Local>);

    impl GenKill<Local> for Anticipated {
        #[inline]
        fn gen(&mut self, elem: Local) {
            self.0.gen(elem)
        }
        #[inline]
        fn kill(&mut self, _: Local) {
            // Ignore borrow invalidation.
        }
    }

    let mut anticipated = Anticipated(BitSet::new_empty(body.local_decls.len()));
    TransferFunction { trans: &mut anticipated }.visit_body(body);
    anticipated.0
}