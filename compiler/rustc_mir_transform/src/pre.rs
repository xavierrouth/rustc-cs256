// Partial Redundancy Elimination
#![allow(unused_imports)]
#[allow(rustc::default_hash_types)]
use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::mir::{
    self, CallReturnPlaces, Local, Location, Place, StatementKind, TerminatorEdges,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
#[allow(rustc::default_hash_types)]
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use rustc_index::bit_set::{BitSet, ChunkedBitSet};
use rustc_index::Idx;

use crate::pre::lattice::Dual;
use crate::IndexVec;

use rustc_mir_dataflow::drop_flag_effects_for_function_entry;
use rustc_mir_dataflow::drop_flag_effects_for_location;
use rustc_mir_dataflow::elaborate_drops::DropFlagState;
use rustc_mir_dataflow::impls::AvailableExpressions;
use rustc_mir_dataflow::impls::PostponableExpressions;
use rustc_mir_dataflow::impls::UsedExpressions;
use rustc_mir_dataflow::impls::{postponable, AnticipatedExpressions};
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

use rustc_mir_dataflow::impls::pre_analysis::{ExprHashMap, ExprIdx, ExprSetElem};

use rustc_mir_dataflow::Results;

type AnticipatedExpressionsResults<'tcx> = Results<'tcx, AnticipatedExpressions>;
type AvailableExpressionsResults<'tcx> = Results<'tcx, AvailableExpressions<'tcx>>;
type PostponableExpressionsResults<'tcx> = Results<'tcx, PostponableExpressions<'tcx>>;

type Domain = BitSet<ExprIdx>;

pub struct PartialRedundancyElimination;

impl<'tcx> PartialRedundancyElimination {
    #[allow(rustc::default_hash_types)]
    fn terminal_blocks(&self, body: &Body<'tcx>) -> HashSet<BasicBlock> {
        let mut terminals = HashSet::new();
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            if let TerminatorEdges::None = block_data.terminator().edges() {
                terminals.insert(block);
            }
        }
        terminals
    }
    #[allow(rustc::default_hash_types)]
    fn compute_earliest(
        &self,
        body: &mut Body<'tcx>,
        anticipated_exprs: AnticipatedExpressionsResults<'tcx>,
        available_exprs: AvailableExpressionsResults<'tcx>,
        #[allow(rustc::default_hash_types)] terminal_blocks: HashSet<BasicBlock>,
    ) -> IndexVec<BasicBlock, Dual<Domain>> {
        let set_diff = |i: BasicBlock| -> Dual<Domain> {
            let anticipated = anticipated_exprs.entry_set_for_block(i);
            let size: usize = anticipated.0.domain_size();
            let available = available_exprs.entry_set_for_block(i);
            // println!("anticipated: {:?}", anticpated.clone());
            // println!("available: {:?}", available.clone());

            let mut earliest = if terminal_blocks.contains(&i) {
                Dual(BitSet::new_empty(size))
            } else {
                anticipated.clone()
            };

            earliest.0.subtract(&available.0);
            // println!("earliest: {:?}", earliest.clone());
            earliest
        };

        let earliest_exprs: IndexVec<_, Dual<BitSet<_>>> =
            IndexVec::from_fn_n(set_diff, body.basic_blocks.len());

        // println!("earliest_results: {:?} ", earliest_exprs);
        earliest_exprs
    }

    #[allow(rustc::default_hash_types)]
    #[allow(rustc::potential_query_instability)]
    fn compute_latest(
        &self,
        body: &mut Body<'tcx>,
        expr_table: Rc<RefCell<ExprHashMap>>,
        earliest_exprs: IndexVec<BasicBlock, Dual<Domain>>,
        postponable_exprs: PostponableExpressionsResults<'tcx>,
    ) -> IndexVec<BasicBlock, Domain> {
        // No dual as confluence is union for Used

        #[allow(rustc::potential_query_instability)]
        // ALGO
        // 0. have bools for earliest and postponable
        // 1. iterate over both for current BB and get exprs
        // 2.a check if used in this BB (need to figure out how to get the BB an Expr is used in)
        // 2.a maybe store this in shared HashMap as well?
        // 2.b OR check if there is some successor of B for which (1) does not hold
        let terminal_blocks = expr_table.as_ref().borrow().terminal_blocks.clone(); // println!("anticipated: {:?}", anticpated.clone());

        // this is just so everything compiles, but define this within closure
        let is_latest = |i: BasicBlock| -> Domain {
            let postponable = postponable_exprs.entry_set_for_block(i);
            let size: usize = postponable.0.domain_size();
            let exprs_in_bb =
                expr_table.as_ref().borrow_mut().bb_expr_map.entry(i).or_default().clone();
            for expr in exprs_in_bb.iter() {
                if earliest_exprs[i].0.contains(*expr) || postponable.0.contains(*expr) {
                    println!("CHECK 1 for latest passed by {:?} in {:?}", *expr, i);
                }
            }
            // println!("available: {:?}", available.clone());
            /* println!(
                "The Exprs in BB {:?} are {:?}",
                i,
                expr_table.as_ref().borrow_mut().bb_expr_map.entry(i).or_default()
            ); */

            let latest = if terminal_blocks.contains(&i) {
                BitSet::new_empty(size)
            } else {
                earliest_exprs[i].0.clone()
            };

            latest
        };

        let latest_exprs: IndexVec<_, BitSet<_>> =
            IndexVec::from_fn_n(is_latest, body.basic_blocks.len());
        latest_exprs
    }
}
impl<'tcx> MirPass<'tcx> for PartialRedundancyElimination {
    fn is_enabled(&self, _sess: &rustc_session::Session) -> bool {
        false //sess.mir_opt_level() >= 1
    }

    #[instrument(level = "trace", skip(self, tcx, body))]
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        debug!(def_id = ?body.source.def_id());
        println!("Body that analysis is running on {:?}", &body.source.def_id());
        println!("----------------ANTICIPATED DEBUG BEGIN----------------");
        let expr_hash_map = Rc::new(RefCell::new(ExprHashMap::new()));

        let terminal_blocks = self.terminal_blocks(body);
        let anticipated = AnticipatedExpressions::new(body, expr_hash_map.clone())
            .into_engine(tcx, body)
            .pass_name("anticipated_exprs")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        println!("----------------ANTICIPATED DEBUG END----------------\n\n\n");

        let _state = anticipated.get();

        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            //anticipated.seek_to_block_end(bb);
            println!("----------- {:?} ----------- ", bb);

            println!(
                "entry set for block {:?} : {:?}",
                bb,
                anticipated.results().entry_set_for_block(bb)
            );
            //anticipated.seek_to_block_start(bb);
        }

        /* for (bb, _block) in body.basic_blocks.iter_enumerated() {
            // anticipated.seek_to_block_end(block);
            let state = anticipated.get();
            // anticipated.results().analysis.fmt_domain(state);
            println!("state {:?}", state);
            println!(
                "entry set for block {:?} : {:?}",
                bb,
                anticipated.results().entry_set_for_block(bb)
            );
            println!(
                "anticipated at end of current block {:?} : {:?}",
                bb,
                anticipated.seek_to_block_start(bb)
            );
            println!(
                "anticipated at start of current block {:?} : {:?}",
                bb,
                anticipated.seek_to_block_end(bb)
            );
        } */

        /*
        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            // anticipated.seek_to_block_end(block);
            println!("----------- {:?} ----------- ", bb);
            let mut state = anticipated.get();
            // anticipated.results().analysis.fmt_domain(state);
            println!("before seek state {:?}", state);
            println!(
                "entry set for block {:?} : {:?}",
                bb,
                anticipated.results().entry_set_for_block(bb)
            );
            /* println!(
                "anticipated at end of current block {:?} : {:?}",
                bb,
                anticipated.seek_to_block_start(bb)
            ); */
            anticipated.seek_to_block_start(bb);
            state = anticipated.get();
            // anticipated.results().analysis.fmt_domain(state);
            println!("start of BB seek state {:?}", state);
            /* println!(
                "anticipated at start of current block {:?} : {:?}",
                bb,
                anticipated.seek_to_block_end(bb)
            ); */
            anticipated.seek_to_block_end(bb);

            state = anticipated.get();
            // anticipated.results().analysis.fmt_domain(state);
            println!("end of BB seek state {:?}", state);
            println!("----------- {:?} ----------- \n\n\n", bb);
        }  */

        println!("----------------AVAILABLE DEBUG BEGIN----------------");
        let available =
            AvailableExpressions::new(body, expr_hash_map.clone(), anticipated.results().clone())
                .into_engine(tcx, body)
                .pass_name("available_exprs")
                .iterate_to_fixpoint()
                .into_results_cursor(body);
        println!("----------------AVAILABLE DEBUG END----------------\n\n\n");

        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            // available.seek_to_block_end(bb);
            println!("----------- {:?} ----------- ", bb);
            let _state = available.get();
            // anticipated.results().analysis.fmt_domain(state);
            println!(
                "entry set for block {:?} : {:?}",
                bb,
                available.results().entry_set_for_block(bb)
            );
            // available.seek_to_block_start(bb);
        }

        let earliest = self.compute_earliest(
            body,
            anticipated.results().clone(),
            available.results().clone(),
            terminal_blocks.clone(),
        );
        println!("----------------POSTPONABLE DEBUG BEGIN----------------");
        let postponable =
            PostponableExpressions::new(body, expr_hash_map.clone(), earliest.clone())
                .into_engine(tcx, body)
                .pass_name("postponable_exprs")
                .iterate_to_fixpoint()
                .into_results_cursor(body);
        println!("----------------POSTPONABLE DEBUG END----------------\n\n\n");

        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            // available.seek_to_block_end(bb);
            println!("----------- {:?} ----------- ", bb);
            // anticipated.results().analysis.fmt_domain(state);
            println!(
                "entry set for block {:?} : {:?}",
                bb,
                postponable.results().entry_set_for_block(bb)
            );
            // available.seek_to_block_start(bb);
        }

        let latest = self.compute_latest(
            body,
            expr_hash_map.clone(),
            earliest.clone(),
            postponable.results().clone(),
        );

        println!("latest {:?}", latest);
    }
}
