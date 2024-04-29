// Partial Redundancy Elimination
#![allow(unused_imports)]
use rustc_middle::mir::visit::MutVisitor;
#[allow(rustc::default_hash_types)]
use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::mir::{
    self, CallReturnPlaces, Local, Location, Place, StatementKind, TerminatorEdges,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Span;
#[allow(rustc::default_hash_types)]
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
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

use itertools::Itertools;
use rustc_data_structures::graph::WithSuccessors;

type AnticipatedExpressionsResults<'tcx> = Results<'tcx, AnticipatedExpressions>;
type AvailableExpressionsResults<'tcx> = Results<'tcx, AvailableExpressions<'tcx>>;
type PostponableExpressionsResults<'tcx> = Results<'tcx, PostponableExpressions<'tcx>>;

type Domain = BitSet<ExprIdx>;

#[allow(rustc::default_hash_types)]
pub struct TempVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    temp_map: &'a HashMap<ExprIdx, Local>,
    temp_rvals_map: &'a mut HashMap<Local, (Rvalue<'tcx>, Span)>,
    expr_hash_map: Rc<RefCell<ExprHashMap>>,
    temps: &'a BitSet<ExprIdx>,
    used_out: &'a BitSet<ExprIdx>,
    latest: &'a BitSet<ExprIdx>
}

#[allow(dead_code)]
#[allow(rustc::default_hash_types)]
impl<'tcx, 'a> TempVisitor<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        temp_map: &'a HashMap<ExprIdx, Local>,
        temp_rvals_map: &'a mut HashMap<Local, (Rvalue<'tcx>, Span)>,
        expr_hash_map: Rc<RefCell<ExprHashMap>>,
        temps: &'a BitSet<ExprIdx>,
        used_out: &'a BitSet<ExprIdx>,
        latest: &'a BitSet<ExprIdx>
    ) -> Self {
        TempVisitor{ tcx, temp_map, temp_rvals_map, expr_hash_map, temps, used_out, latest }
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for TempVisitor<'tcx, 'a> {

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    
    fn visit_statement(&mut self, statement: &mut Statement<'tcx>, _: Location) {
        // We need some way of dealing with constants
        if let StatementKind::Assign(box (_, ref mut rvalue)) = statement.kind {

            if let Rvalue::BinaryOp(bin_op, box(operand1, operand2)) = rvalue { 
                if let (Some(Place { local: local1, .. }), Some(Place { local: local2, .. })) =
                (operand1.place(), operand2.place())
                {
                    if let Some(expr_idx) = self.expr_hash_map.as_ref().borrow().expr_idx(ExprSetElem {
                        bin_op: *bin_op,
                        local1,
                        local2,
                    }) {
                        // If expr_idx in Latest and Out Used, add temporary to beginning of basic block
                        if self.temps.contains(expr_idx) {
                            //
                            println!("Adding Temporary for: {:?}", expr_idx);
                            self.temp_rvals_map.entry(self.temp_map[&expr_idx]).or_insert((rvalue.clone(), statement.source_info.span.clone()));
                        }
                        // FIXME: This is replacing stuff that isn't marked as used? 
                        // Replace expression with temp if not in Latest or in Out Used
                        if self.used_out.contains(expr_idx) || !self.latest.contains(expr_idx) {
                            println!("Replacing {:?} with temp", expr_idx);
                            *rvalue = Rvalue::Use(Operand::Copy(self.temp_map[&expr_idx].into()));
                        }
                    }
                }
            }
        }
    }
}

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
        // According to the UCSB slides, the criteria for Latest is pretty well-defined:
        //  1. Expression must be in earliest or postponable
        //  2. Expression must be in used or NOT in any successors' earliests or 
        let mut latest_exprs = IndexVec::from_elem(Domain::new_empty(postponable_exprs.analysis.domain_size(body)), &body.basic_blocks);
        let mut ok_to_place_succ = IndexVec::from_elem(Domain::new_filled(postponable_exprs.analysis.domain_size(body)), &body.basic_blocks);
        for (bb, _) in traversal::postorder(body) {
            // Might not even need to clone, as we won't use earliest again afterwards
            let mut ok_to_place = earliest_exprs[bb].0.clone();
            // println!("{:?} vs. {:?} vs. {:?}\n", ok_to_place.domain_size(), earliest_exprs[bb].0.domain_size(), postponable_exprs.entry_set_for_block(bb).0.domain_size());
            ok_to_place.union(&postponable_exprs.entry_set_for_block(bb).0);
            for expr in ok_to_place.iter() {
                if expr_table.as_ref().borrow_mut().bb_expr_map.entry(bb).or_default().contains(&expr) || !ok_to_place_succ[bb].contains(expr) {
                    latest_exprs[bb].insert(expr);
                }
            }
            for pred_bb in body.basic_blocks.predecessors()[bb].iter() {
                ok_to_place_succ[*pred_bb].intersect(&ok_to_place);
            }
        }
        latest_exprs
    }
}

#[allow(unused_mut)]
#[allow(rustc::default_hash_types)]
impl<'tcx> MirPass<'tcx> for PartialRedundancyElimination {
    fn is_enabled(&self, _sess: &rustc_session::Session) -> bool {
        false //sess.mir_opt_level() >= 1
    }

    #[allow(unused_mut)]
    #[allow(rustc::potential_query_instability)]
    #[instrument(level = "trace", skip(self, tcx, body))]
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        //let debug_info = 0;

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

        println!("Anticipated:");
        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            //anticipated.seek_to_block_end(bb);

            println!(
                "entry set for block {:?} : {:?}",
                bb,
                anticipated.results().entry_set_for_block(bb)
            );
            //anticipated.seek_to_block_start(bb);
        }

        println!("----------------AVAILABLE DEBUG BEGIN----------------");
        let available =
            AvailableExpressions::new(body, expr_hash_map.clone(), anticipated.results().clone())
                .into_engine(tcx, body)
                .pass_name("available_exprs")
                .iterate_to_fixpoint()
                .into_results_cursor(body);
        println!("----------------AVAILABLE DEBUG END----------------\n\n\n");

        println!("Available:");
        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            // available.seek_to_block_end(bb);
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
        
        println!("Postponable:");
        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            // available.seek_to_block_end(bb);
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
        println!("earliest : {earliest:?}");
        println!("latest : {:?}", latest);

        println!("----------------USED DEBUG BEGIN----------------");
        let mut used = UsedExpressions::new(body, expr_hash_map.clone(), latest.clone())
            .into_engine(tcx, body)
            .pass_name("used_exprs")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        println!("----------------USED DEBUG END----------------\n\n\n");

        println!("Used:");
        for (bb, _block) in body.basic_blocks.iter_enumerated() {
            // available.seek_to_block_end(bb);
            // anticipated.results().analysis.fmt_domain(state);
            println!("entry set for block {:?} : {:?}", bb, used.results().entry_set_for_block(bb));
            // available.seek_to_block_start(bb);
        }

        println!("Transforming the code");
        
        let mut temp_map = HashMap::<ExprIdx, Local>::new();
        let mut local_cnt = body.local_decls().len();

        let mut used_map = HashMap::<BasicBlock, BitSet<ExprIdx>>::new();
        
        let reverse_postorder = body.basic_blocks.reverse_postorder().to_vec();

        for bb in reverse_postorder.clone() {
            
            // Generate Local temporaries for block
            // We will assign them to the proper rvalues later
            //used.seek_to_block_end(bb);
            used.seek_to_block_start(bb);
            let used_out = used.get().clone();
            used_map.entry(bb).or_insert(used_out);
            // Replace expressions in bb with temporaries
        }

        for bb in reverse_postorder {
            let data = &mut body.basic_blocks.as_mut_preserves_cfg()[bb];
            let used_out = used_map.get(&bb).expect("Oh Nohgawjkegh!");
            println!("Used out for bb {:?}: {:?}, {:?}", bb, used_out, used_out.domain_size());
            let mut temps = used_out.clone();
            let latest_set = latest.get(bb).expect("Not latest");
            println!("Latest for bb {:?}: {:?}, {:?}", bb, latest_set, latest_set.domain_size());
            temps.intersect(latest_set);
            let mut temp_rvalues = HashMap::<Local, (Rvalue<'_ >, Span)>::new();
            for expr in temps.iter() {
                println!("Inserting temp");
                let temp = Local::new(local_cnt);
                local_cnt += 1;
                temp_map.insert(expr, temp);
            }

            let mut temp_visitor = TempVisitor::new(
                tcx, &temp_map, &mut temp_rvalues, expr_hash_map.clone(), &temps, &used_out, &latest[bb]);
            temp_visitor.visit_basic_block_data(bb, data);
            
            // FIXME: Get the type of this expression correctly
            let ty = body.local_decls[Local::new(0)].ty;

            // Define temp
            // Add temporary assignments to basic block
            #[allow(rustc::potential_query_instability)]
            let _ = temp_rvalues.iter().for_each(|(temp, (rvalue, span))| {
                println!("local: {:?}, rvalue {:?}", temp, rvalue);
                let local_decl = LocalDecl::new(ty, *span);
                body.local_decls.push(local_decl); // Jump hope this index returned from here is the same as calculated via local_cnt
                data.statements.insert(0, // Insert in correct spot.
                    Statement { 
                        source_info: SourceInfo::outermost(*span), 
                        kind: StatementKind::Assign(Box::new((Into::into(*temp), rvalue.clone())))});
            });
        }

    }
}
