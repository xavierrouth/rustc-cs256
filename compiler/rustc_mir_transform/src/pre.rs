// Partial Redundancy Elimination
#![allow(unused_imports, unreachable_code, dead_code, unused_variables)]
use rustc_middle::middle::stability::Index;
use rustc_middle::mir::graphviz::write_mir_fn_graphviz;
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
use rustc_middle::ty::List;
use std::fs::File;
use rustc_index::bit_set::{BitSet, ChunkedBitSet};
use rustc_index::Idx;

use crate::pre::lattice::Dual;
use crate::IndexVec;

use rustc_mir_dataflow::drop_flag_effects_for_function_entry;
use rustc_mir_dataflow::drop_flag_effects_for_location;
use rustc_mir_dataflow::elaborate_drops::DropFlagState;
use rustc_mir_dataflow::impls::AvailableExpressions;
use rustc_mir_dataflow::impls::AvailableExpressionsResults;
use rustc_mir_dataflow::impls::AnticipatedExpressionsResults;

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

type PostponableExpressionsResults<'tcx> = Results<'tcx, PostponableExpressions<'tcx>>;

type Domain = BitSet<ExprIdx>;

#[allow(rustc::default_hash_types)]
pub struct TempVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    temp_map: &'a HashMap<ExprIdx, Local>,
    // temp_rvals_map: &'a mut HashMap<Local, (Rvalue<'tcx>, Span)>,
    expr_hash_map: Rc<RefCell<ExprHashMap>>,
    // temps: &'a BitSet<ExprIdx>,
    used_out: &'a BitSet<ExprIdx>,
    latest: &'a BitSet<ExprIdx>
}

#[allow(dead_code)]
#[allow(rustc::default_hash_types)]
impl<'tcx, 'a> TempVisitor<'tcx, 'a> {
    /* 
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
    } */


    pub fn new(
        tcx: TyCtxt<'tcx>,
        temp_map: &'a HashMap<ExprIdx, Local>,
        expr_hash_map: Rc<RefCell<ExprHashMap>>,
        used_out: &'a BitSet<ExprIdx>,
        latest: &'a BitSet<ExprIdx>
    ) -> Self {
        TempVisitor{ tcx, temp_map, expr_hash_map, used_out, latest }
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

    fn preprocess_blocks(&self, body: &mut Body<'tcx>) {
        // Find predecessors, and terminators to insert
        struct InsertionInfo {
            source: BasicBlock,
            dest: BasicBlock
        }

        let mut to_insert = Vec::new();

        // Fixme: What if a terminator can go to the same node on multiple edges.

        for (bb_dest, dest) in body.basic_blocks.iter_enumerated() {
            let all_predecessors = body.basic_blocks.predecessors();
            // Insert blocks w/ multiple predecessors.
            let preds = &all_predecessors[bb_dest];
            if preds.len() > 1 {
                for p in preds {
                    let info = InsertionInfo {
                        source: *p,
                        dest: bb_dest
                    };
                    to_insert.push(info);
                }
            }
        }
        // body.

        

        for InsertionInfo {source, dest} in to_insert {
            // Fixme: Is there a better way to get a terminator?
           
            let source_info = SourceInfo::outermost(body.span);
            let terminator = Terminator {source_info, kind: TerminatorKind::Goto {target: dest}}; 
            let new_block_data = BasicBlockData::new(Some(terminator)); 

            let blocks = body.basic_blocks.as_mut();
            let new_block: BasicBlock = blocks.push(new_block_data);

            // Edit old terminator
            let old_terminator = body[source].terminator_mut();

            match &mut old_terminator.kind {
                TerminatorKind::Goto { target } => {
                    old_terminator.kind = TerminatorKind::Goto{target: new_block};
                },
                TerminatorKind::SwitchInt { discr, ref mut targets } => {
                    for target in targets.all_targets_mut() {
                        if *target == dest {
                            *target = new_block;
                        }
                    }
                }
                TerminatorKind::UnwindResume => todo!(),
                TerminatorKind::UnwindTerminate(_) => todo!(),
                TerminatorKind::Return => (), //todo!(),
                TerminatorKind::Unreachable => todo!(),
                TerminatorKind::Drop { place, target, unwind, replace } => todo!(),
                TerminatorKind::Call { func, args, destination, target, unwind, call_source, fn_span } => todo!(),
                TerminatorKind::Assert { cond, expected, msg, target, unwind } => todo!(),
                TerminatorKind::Yield { value, resume, resume_arg, drop } => todo!(),
                TerminatorKind::CoroutineDrop => todo!(),
                TerminatorKind::FalseEdge { real_target, imaginary_target } => todo!(),
                TerminatorKind::FalseUnwind { real_target, unwind } => todo!(),
                TerminatorKind::InlineAsm { template, operands, options, line_spans, destination, unwind } => todo!(),
            }
        }
        
        // BasicBlockData::new()
        

    }

    #[allow(rustc::default_hash_types)]
    fn compute_earliest(
        &self,
        body: &mut Body<'tcx>,
        anticipated_exprs: AnticipatedExpressionsResults,
        available_exprs: AvailableExpressionsResults,
        #[allow(rustc::default_hash_types)] terminal_blocks: HashSet<BasicBlock>,
    ) -> IndexVec<BasicBlock, Dual<Domain>> {
        let set_diff = |i: BasicBlock| -> Dual<Domain> {
            let anticipated = anticipated_exprs.get(i).expect("in compute earliest");
            let size: usize = anticipated.0.domain_size();
            // FIXME: anticipated and available were both 'entry set for block';
            let available = available_exprs.get(i).expect("awdawd");
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
        let mut before_file = File::create("before.dot").unwrap();
        let _ = write_mir_fn_graphviz(tcx, body, false, &mut before_file).expect("failed to write before file");

        debug!(def_id = ?body.source.def_id());
        println!("Body that analysis is running on {:?}", &body.source.def_id());

        self.preprocess_blocks(body);

        println!("----------------ANTICIPATED DEBUG BEGIN----------------");
        let expr_hash_map = Rc::new(RefCell::new(ExprHashMap::new()));

        let terminal_blocks = self.terminal_blocks(body);
        let mut anticipated = AnticipatedExpressions::new(body, expr_hash_map.clone())
            .into_engine(tcx, body)
            .pass_name("anticipated_exprs")
            .iterate_to_fixpoint()
            .into_results_cursor(body);
        println!("----------------ANTICIPATED DEBUG END----------------\n\n\n");

        let state = anticipated.get();

        let size = state.0.domain_size(); // Fixme 
        let mut anticipated_exprs: IndexVec<BasicBlock, Dual<BitSet<_>>> = IndexVec::from_elem(Dual(BitSet::new_empty(size)), &body.basic_blocks);
        let mut anticipated_exprs_end: IndexVec<BasicBlock, Dual<BitSet<_>>> = IndexVec::from_elem(Dual(BitSet::new_empty(size)), &body.basic_blocks);

        
        for (bb, _block) in body.basic_blocks.iter_enumerated() {

            anticipated.seek_to_block_start(bb);

            let set = anticipated.get();
            anticipated_exprs[bb] = set.clone();

            anticipated.seek_to_block_end(bb);

            let set = anticipated.get();
            anticipated_exprs_end[bb] = set.clone();

        }

        println!("Anticipated:");
                // Print loop
        for (bb, set) in anticipated_exprs.iter_enumerated() {
            println!(
                "set for block {:?} : {:?}",
                bb,
                set
            );
        }

        println!("----------------AVAILABLE DEBUG BEGIN----------------");
        let mut available =
            AvailableExpressions::new(body, expr_hash_map.clone(), anticipated_exprs_end.clone())
                .into_engine(tcx, body)
                .pass_name("available_exprs")
                .iterate_to_fixpoint()
                .into_results_cursor(body);
        println!("----------------AVAILABLE DEBUG END----------------\n\n\n");


        let mut available_exprs: IndexVec<BasicBlock, Dual<BitSet<_>>> = IndexVec::from_elem(Dual(BitSet::new_empty(size)), &body.basic_blocks);
        let mut available_exprs_start: IndexVec<BasicBlock, Dual<BitSet<_>>> = IndexVec::from_elem(Dual(BitSet::new_empty(size)), &body.basic_blocks);


        // Gather loop
        for (bb, _block) in body.basic_blocks.iter_enumerated() {

            available.seek_to_block_start(bb);
            let set = available.get();
            available_exprs_start[bb] = set.clone();

            available.seek_to_block_end(bb);
            let set = available.get();
            available_exprs[bb] = set.clone();
        }

        println!("Available:");
        // Print loop
        for (bb, set) in available_exprs.iter_enumerated() {
            println!(
                "in set for block {:?} : {:?}",
                bb,
                available_exprs_start[bb]
            );
            println!(
                "out set for block {:?} : {:?}",
                bb,
                set
            );
        }

        let earliest = self.compute_earliest(
            body,
            anticipated_exprs.clone(), // Anticipated at start.
            available_exprs_start.clone(), // Available at end. // This should be available start
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
        
        // Map 
        let mut temp_map = HashMap::<ExprIdx, Local>::new();
        // Number of locals. 
        // let mut local_cnt = body.local_decls().len();

        // let bb_count = body.basic_blocks.len();
        let mut expr_type_table: HashMap<ExprIdx, Ty<'tcx>> = HashMap::new();

        for (bb, data) in body.basic_blocks.iter_enumerated() {
            for stmt in &data.statements {
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
                                let expr_idx = expr_hash_map.as_ref().borrow_mut().expr_idx_mut(ExprSetElem {
                                    bin_op: *bin_op,
                                    local1,
                                    local2,
                                });
                                
                                expr_type_table.insert(expr_idx, body.local_decls[place.local].ty);
                            }
                        }

                        _ => {}
                    }

                }
            }
        }

        let mut used_map = HashMap::<BasicBlock, BitSet<ExprIdx>>::new();
        
        let mut expressions_to_insert = HashMap::<BasicBlock, (Local, ExprIdx)>::new();

        let reverse_postorder = body.basic_blocks.reverse_postorder().to_vec();

        // Preprocessing
        for bb in reverse_postorder.clone() {
            // Seperate 'used' cursor from a shared ref of block

            //used.seek_to_block_end(bb);
            // used.seek_to_block_start(bb); // This is the out set
            let used_out = used.results().entry_set_for_block(bb); // get().clone();
            used_map.entry(bb).or_insert(used_out.clone());
        }
        
        // Rule 1:
        for bb in reverse_postorder.clone() {
            let used_out = used_map.get(&bb).expect("Oh Nohgawjkegh!");
            let mut temps = used_out.clone();
            let latest_set = latest.get(bb).expect("Not latest");
            temps.intersect(latest_set);

            println!("temps for bb {:?} : {:?}", bb, temps);
            
            
            for expr in temps.iter() {
                println!("Inserting temp for {:?}", expr);


                // Map this expression to the new temp for use in pass 2.
                // SURELY THERE IS .entry().or_insert_fn(|a| { body of entry::vacant(a)} )
                let temp_local = match temp_map.entry(expr.clone()) {
                    std::collections::hash_map::Entry::Occupied(tmp) => {
                        tmp.get().clone()
                    }
                    std::collections::hash_map::Entry::Vacant(a) => {
                        //let ty = body.local_decls[Local::new(0)].ty; // FIXME: Get type better.
                        let ty = expr_type_table.get(&expr).expect("UH OH TYPE MISSING");

                        let span = body.span;
        
                        let local_decl = LocalDecl::new(*ty, span);
                        let temp = body.local_decls.push(local_decl);

                        a.insert(temp).clone()
                    }
                };

                // Remember to insert an assignment to the local 'temp', we will derive the expression from the epxr idx later.
                expressions_to_insert.insert(bb, (temp_local, expr));
            }
        }

        // Rule 2:
        for bb in reverse_postorder.clone() {
            let data = &mut body.basic_blocks.as_mut_preserves_cfg()[bb];
            let used_out = used_map.get(&bb).expect("Oh Nohgawjkegh!");
            let latest_set = latest.get(bb).expect("Not latest");


            // println!("temps for bb {:?} : {:?}", bb, temps);
            
            // Get all uses of expressions. 
            // Get uses for this BB. 
            // Run visitor:

            // Corny
            // 
            // let mut temp_rvalues = HashMap::<Local, (Rvalue<'_ >, Span)>::new();

            let mut visitor = TempVisitor::new(
                tcx, &temp_map, expr_hash_map.clone(), &used_out, &latest_set
            );

            // Replace expression with temp if not in Latest or in Out Used
            visitor.visit_basic_block_data(bb, data);
        }

        let expr_map = &expr_hash_map.borrow().expr_table;

        let reverse_expr_map: HashMap<ExprIdx, ExprSetElem> = expr_map.iter()
            .map(|(k, v)| (v.clone(), k.clone())).collect();

        let span = body.span;
        // Generate assignments
        for (bb, (temp, expr)) in expressions_to_insert.iter() {
            let data = &mut body.basic_blocks.as_mut_preserves_cfg()[*bb];
            let expression = reverse_expr_map.get(expr).expect("rvalue not found"); // Might need to generate this expression again, not sure if i can just summon it on the fly.
            let ExprSetElem {bin_op, local1, local2} = expression;

            let op1 = Operand::Copy(Place {local: *local1, projection: List::empty() });
            let op2 = Operand::Copy(Place {local: *local2, projection: List::empty() });
            // let op1 = // Copy(Place<'tcx>),

            let rvalue = Rvalue::CheckedBinaryOp(*bin_op,  Box::new((op1, op2)));
            
            data.statements.insert(0, // FIXME: Insert in correct spot.
                Statement { 
                    source_info: SourceInfo::outermost(span), 
                    kind: StatementKind::Assign(Box::new((Into::into(*temp), rvalue.clone())))});
        }

        let mut after_file = File::create("after.dot").unwrap();
        write_mir_fn_graphviz(tcx, body, false, &mut after_file).expect("failed to write after file");
    }
}

impl<'tcx, 'a> MutVisitor<'tcx> for TempVisitor<'tcx, 'a> {

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    
    fn visit_statement(&mut self, statement: &mut Statement<'tcx>, _: Location) {
        // We need some way of dealing with constants
        if let StatementKind::Assign(box (_, ref mut rvalue)) = statement.kind {
            match rvalue { Rvalue::BinaryOp(bin_op, box(operand1, operand2))
                | Rvalue::CheckedBinaryOp(bin_op, box (operand1, operand2)) =>
            
                if let (Some(Place { local: local1, .. }), Some(Place { local: local2, .. })) =
                (operand1.place(), operand2.place())
                {
                    if let Some(expr_idx) = self.expr_hash_map.as_ref().borrow().expr_idx(ExprSetElem {
                        bin_op: *bin_op,
                        local1,
                        local2,
                    }) {
                        println!("Statement has expression: {:?}", expr_idx);
                        // If expr_idx in Latest and Out Used, add temporary to beginning of basic block

                        // Replace expression with temp if not in Latest or in Out Used
                        if self.used_out.contains(expr_idx) || !self.latest.contains(expr_idx) {
                            let temp = self.temp_map.get(&expr_idx); 
                            if let Some(temp) = temp {
                                println!("Replacing {:?} with temp", expr_idx);
                                *rvalue = Rvalue::Use(Operand::Copy((*temp).into()));
                            } else {
                                println!("no temp for {:?} ejalkwehjg", expr_idx);
                            }
                            
                        }
                    }
                }
                _ => {}
            }
             
        }
    } 
    
    /*
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
                        println!("Statement has expression: {:?}", expr_idx);
                        println!("temps: {:?}", self.temps);
                        // If expr_idx in Latest and Out Used, add temporary to beginning of basic block
                        if self.temps.contains(expr_idx) {
                            //
                            println!("Adding Temporary for: {:?}", expr_idx);
                            self.temp_rvals_map.entry(self.temp_map[&expr_idx]).or_insert((rvalue.clone(), statement.source_info.span.clone()));
                        }
                        // Replace expression with temp if not in Latest or in Out Used
                        if self.used_out.contains(expr_idx) || !self.latest.contains(expr_idx) {
                            let temp = self.temp_map.get(&expr_idx); 
                            if let Some(temp) = temp {
                                println!("Replacing {:?} with temp", expr_idx);
                                *rvalue = Rvalue::Use(Operand::Copy((*temp).into()));
                            } else {
                                println!("no temp for {:?} ejalkwehjg", expr_idx);
                            }
                            
                        }
                    }
                }
            }
             
        } 
    } */
}
