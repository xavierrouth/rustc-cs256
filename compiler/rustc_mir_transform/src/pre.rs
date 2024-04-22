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
use rustc_mir_dataflow::impls::{
    AnticipatedExpressions, // AvailableExpressions
};

pub struct PartialRedundancyElimination;

impl<'tcx> MirPass<'tcx> for PartialRedundancyElimination {
    fn is_enabled(&self, _sess: &rustc_session::Session) -> bool {
        false //sess.mir_opt_level() >= 1
    }

    #[instrument(level = "trace", skip(self, tcx, body))]
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        debug!(def_id = ?body.source.def_id());
        println!("running PRE on {:?}", body.source.def_id());
        let _anticipated = AnticipatedExpressions::new(body)
            .into_engine(tcx, body)
            .pass_name("anticipated_exprs")
            .iterate_to_fixpoint()
            .into_results_cursor(body);

        /*
        let _available = AvailableExpressions::new(body, _anticipated)
            .into_engine(tcx, body)
            .pass_name("available_exprs")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        */
    }
}
