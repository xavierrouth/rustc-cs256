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

use rustc_mir_dataflow::drop_flag_effects_for_function_entry;
use rustc_mir_dataflow::drop_flag_effects_for_location;
use rustc_mir_dataflow::elaborate_drops::DropFlagState;
use rustc_mir_dataflow::impls::AnticipatedExpressions;
use rustc_mir_dataflow::impls::AvailableExpressions;
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

pub struct PartialRedundancyElimination;

impl<'tcx> MirPass<'tcx> for PartialRedundancyElimination {
    fn is_enabled(&self, _sess: &rustc_session::Session) -> bool {
        false //sess.mir_opt_level() >= 1
    }

    #[instrument(level = "trace", skip(self, tcx, body))]
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        debug!(def_id = ?body.source.def_id());
        //println!("Body that analysis is running on {:?}", &body.basic_blocks);
        //println!("----------------ANTICIPATED DEBUG BEGIN----------------");
        let anticipated = AnticipatedExpressions::new(body)
            .into_engine(tcx, body)
            .pass_name("anticipated_exprs")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        //println!("----------------ANTICIPATED DEBUG END----------------\n\n\n");

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
        let mut available = AvailableExpressions::new(body, anticipated)
            .into_engine(tcx, body)
            .pass_name("available_exprs")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        println!("----------------AVAILABLE DEBUG END----------------\n\n\n");

        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            available.seek_to_block_end(bb);
            println!("----------- {:?} ----------- ", bb);
            let _state = available.get();
            // anticipated.results().analysis.fmt_domain(state);
            println!(
                "entry set for block {:?} : {:?}",
                bb,
                available.results().entry_set_for_block(bb)
            );
            available.seek_to_block_start(bb);
        }
    }
}
