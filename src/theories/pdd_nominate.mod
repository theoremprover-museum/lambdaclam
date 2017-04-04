module pdd_nominate.

accumulate arithmetic.

local pdd_nominate_dummy o.
pdd_nominate_dummy.
local pdd_nominate_dummy1 o.
pdd_nominate_dummy1.
local pdd_nominate_dummy2 o.
pdd_nominate_dummy2.

local check_truth osyn -> (list context) -> o.

known_false (app eq [trueP, falseP]) _.
known_false G Context:-
	    sym_eval_rewrites_list List,
	    (((member (banned BList) Context), !, partition_rw BList List _ Rest);            
	    Rest = List), 
         rewrite_with_rules Rest Rule G falseP Cond,
	 log_rewrite_rule Context Rule.

local partition_rw (list A) -> (list A) -> (list A) -> (list A) -> o.
partition_rw [] L [] L.
partition_rw (H::T) List (H::B) C:-
	memb_and_rest H List Rest, !,
	partition_rw T Rest B C.
partition_rw (H::T) List B C:-
	partition_rw T List B C.

ripple_operate error_loc L1 L2:- 
	insert_before fertilise (rewrite_with sym_eval_rewrites_list (R:rewrite_rule)) L1 L3,
	replace fertilise (orelse_meth fertilise (critic_meth pdd_critic_strat)) L3 L4,
	ripple_operate with_critics L4 L2.

local insert_before meth -> meth -> (list meth) -> (list meth) -> o.
insert_before _ B [] [].
insert_before A B (A::T) (B::(A::T)).
insert_before A B (H::T) (H::Tout):-
	      insert_before A B T Tout.

compound_critic pdd_nominate pdd_critic_strat
	(then_crit (pop_critic Address)
	(subplan_crit Address
	(then_crit (pdd_critic NewRule Rule)
		 (continue_crit (m\ close_branch))))).

compound_critic pdd_nominate error_loc_strat
	(then_crit (pop_critic Address)
	(subplan_crit Address
	(then_crit (error_locic 0 NewRule Rule)
		 (continue_crit (m\ close_branch))))).
				

atomic pdd_nominate close_branch
       _
       true
       true
       trueGoal
       notacticyet.

atomic pdd_nominate diagnose_meth
       _
       (get_goal [] (seqGoal _ C),
        poll_context C R,
	 printstdout "WARNING: Possibly Incorrect Rewrite Rule:",
	       printstdout R)
       true
       trueGoal
       notacticyet.

atomic_critic pdd_nominate (pdd_critic Rule R)
	      Ad
	      Agenda
	      (get_goal Ad (seqGoal (H >>> G) C))
%	      (instantiate_gb_context_bad C)
	      true
	      nil
	      Agenda.

atomic_critic pdd_nominate (error_locic 0 Rule R)
	      Ad
	      Agenda
	      (get_goal Ad (seqGoal (H >>> G) C))
	      (check_truth G C,
	      printstdout C,
	       instantiate_gb_context_bad C
	       )
	      nil
	      Agenda.



local map_accum (list A) -> (A -> B -> B -> o) -> B -> B -> o.
map_accum nil P X X.
map_accum (H::T) P Xin Xout:-
	  P H Xin NewX, !,
	  map_accum T P NewX Xout.
	      

local instantiate_gb_context_bad (list context) -> o.
instantiate_gb_context_bad Context:-
	memb_and_rest (unsure X RRINFO) Context Rest, !,
	for_each RRINFO (RINFO\ sigma Rule\ sigma Info\ sigma Used\ (
		RINFO = (rrstatus Rule Info Pointer Used),
		((not (Used = 0), fetch_rr_point Pointer Info (gbleaf bad)); true))),
	instantiate_gb_context_bad Rest.
instantiate_gb_context_bad Context.

local poll_context (list context) ->  rewrite_rule -> o.
poll_context Context R:-
	map_accum Context (Unsure\ Xin\ Xout\ sigma X\ sigma RINFO\ (
		((Unsure = (unsure X RINFO), append RINFO Xin Xout);
		 (not (Unsure = (unsure X RINFO)), Xin = Xout))))

[]  RRINFO,
	mappred2 RRINFO (RINFO\ Rule\ Score\ sigma Info\ sigma Used\ sigma GScore\ sigma BScore\ (
		RINFO = (rrstatus Rule Info Pointer Used),
		(poll_gb_tree Info GScore BScore, 
		  Score = [BScore, GScore]))) Rules Scores,
		max_score Rules Scores _ _ R.
      
local poll_gb_tree good_bad_tree -> int -> int -> o.
poll_gb_tree (gbleaf unknown) 0 0:- !.
poll_gb_tree (gbleaf good) 1 0.
poll_gb_tree (gbleaf bad) 0 1.
poll_gb_tree (gbnode L R) GS BS:-
	     poll_gb_tree L GS1 BS1,
	     poll_gb_tree R GS2 BS2,
	     GS is (GS1 + GS2),
	     BS is (BS1 + BS2).

local max_score (list rewrite_rule) -> (list (list int)) -> (list int) -> rewrite_rule -> rewrite_rule -> o.
max_score [] [] Max R R.
max_score (R::TR) (I::TI) [MaxB, MaxG] RC RO:-	
	  ((I = [BS, GS], 
	  printstdout R,
	  printstdout BS,
	  printstdout GS,
            not(BS = 0), 
	    ((BS = MaxB, (GS = MaxG; GS < MaxG));
	     (BS > MaxB)), !, max_score TR TI [BS, GS] R RO);
	    max_score TR TI [MaxB, MaxG] RC RO).

compound induction (induction_top error_loc) 
	 (then_meth and_i (pair_meth

	 (complete_meth
		(repeat_meth
		(orelse_meth (repeat_meth and_i)
		(orelse_meth trivials
		(orelse_meth allFi
	 	(orelse_meth taut
            	(orelse_meth (cond_meth contains_any_meta_var_goal fail_meth my_sym_eval)
		(orelse_meth (then_meth existential (try_meth my_sym_eval))
		(orelse_meth (repeat_meth generalisation_compound)
                         (ind_strat error_loc)
	)))))))))
	diagnose_meth))
	_
	true.


compound rewriting my_sym_eval
	(repeat_meth 
	(then_meth (cond_meth contains_any_meta_var_goal (try_meth coerce_vars) id_meth)
	(orelse_meth rewrite_with_hyp
	(orelse_meth (orelse_meth
		(rewrite_with sym_eval_rewrites_list (R:rewrite_rule))
			(critic_meth error_loc_strat))
	(orelse_meth (then_meth rewrite_with_transitive_hyp (formula_tester [1,0] evaluate (label_truth _ 0 0)))
	(orelse_meth (rewrite_case_split sym_eval_rewrites_list (R1:rewrite_rule))
	(orelse_meth  redundant

	%% See if some "normalising" by moving implications can occur
	(orelse_meth (then_meth
		(then_meth (try_meth (repeat_meth all_i)) imp_i)
		(then_meth (try_meth (repeat_meth (orelse_meth and_e or_e)))
			 (orelse_meth (rewrite_with sym_eval_rewrites_list (R:rewrite_rule))
			(then_meth (repeat_meth rewrite_with_hyp) 
                         (formula_tester [3,0] evaluate (label_truth _ 0 0))))))

	(orelse_meth and_e or_e)))))))))
      Address
	true.

check_truth (app forall [Type, (abs Goal Type)]) C:-
		pi z\ (has_otype bound z Type => check_truth (Goal z) C).
check_truth G C:-
		known_false G C.

atomic induction fertilisation_strong
	( seqGoal (H >>> trueP) Context)
	(memb_and_rest (hyp H1 ind_hyp) H Rest)
	(filter Context NewContext (C1\ (sigma A\ (sigma B\ (C1 = (embedding_context A B))))),
	 mappred Rest (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce Hyps X Z;
		  Z = X)),
		 B = (hyp Z T))) NewHyps)
	(seqGoal (NewHyps >>> trueP) NewContext)
	notacticyet.

end
