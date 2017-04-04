module pdd_repair.

accumulate lclam.

local pdd_repair_dummy o.
pdd_repair_dummy.
local pdd_repair_dummy1 o.
pdd_repair_dummy1.
local pdd_repair_dummy2 o.
pdd_repair_dummy2.

local check_truth osyn -> o.
local no_rule (list osyn) -> osyn -> (list context) -> osyn  -> o.
local no_rule_applies osyn -> o.
local type_constructor_test osyn -> o.

known_false (app eq [trueP, falseP]).
                                                                                                                             
atomic pdd_repair (introduce_hyp H) 
	(seqGoal (Hyps >>> G) C)
	true
	true
	(seqGoal (((hyp H new_rewrite)::Hyps) >>> G) C)
	notacticyet.

atomic pdd_repair (introduce_hyp_and_ban H R) 
	(seqGoal (Hyps >>> G) C)
	true
	(((memb_and_rest (banned L) C Rest, NewC = ((banned (R::L))::Rest));
	 NewC = ((banned [R])::C)))
	(seqGoal (((hyp H new_rewrite)::Hyps) >>> G) NewC)
	notacticyet.

ripple_operate sym_eval_crit L1 L2:- 
	replace fertilise (orelse_meth fertilise (critic_meth pdd_critic_strat)) L1 L3,
	ripple_operate with_critics L3 L2.

compound_critic pdd_repair pdd_critic_strat
	(then_crit (pop_critic Address)
	(subplan_crit Address
	(then_crit (pdd_critic NewRule Rule)
	     (then_crit roll_back_to_start
	     (subplan_crit [] 
		 (continue_crit 
			  (m\ (then_meth (introduce_hyp_and_ban NewRule Rule)
			      (induction_top sym_eval_crit))))))))).



compound_critic pdd_repair sym_eval_crit_strat
	(then_crit (pop_critic Address)
	(subplan_crit Address
	(orelse_crit (then_crit (sym_eval_critic 0 NewRule Rule)
		     (then_crit roll_back_to_start
		     (subplan_crit [] 
			 (continue_crit 
				  (m\ (then_meth (introduce_hyp_and_ban NewRule
Rule)
				      (induction_top sym_eval_crit)))))))
		     (then_crit (sym_eval_critic 1 NewRule _)
			   (continue_crit
				  (m\ (then_meth (introduce_hyp NewRule) m))))))).

atomic_critic pdd_repair (pdd_critic Rule R)
	      Ad
	      Agenda
	      (get_goal Ad (seqGoal (H >>> G) C))
	      (instantiate_gb_context_bad C,
	       poll_context C R,
	       printstdout "WARNING: Possibly Incorrect Rewrite Rule:",
	       printstdout R, !,
	       definition _ R Cond LHS _,
	       form_rule Cond LHS VarRule,
	       copy_term [VarRule] [CleanVarRule],
	       count_vars CleanVarRule 1 N,
	       N1 is (N - 1),
	       extend_form_rule_rec CleanVarRule RuleSkel N1,
	       create_new_rr RuleSkel Rule N1, !,
	       env_otype Rule H _,
	       printstdout Rule, !
	       )
	      nil
	      Agenda.

atomic_critic pdd_repair (sym_eval_critic 0 Rule R)
	      Ad
	      Agenda
	      (get_goal Ad (seqGoal (H >>> G) C))
	      ((not (not (check_truth G))),
	       instantiate_gb_context_bad C,
	       poll_context C R,
	       printstdout "WARNING: Incorrect Rewrite Rule:",
	       printstdout R,
	       definition _ R Cond LHS _,
	       form_rule Cond LHS VarRule,
	       copy_term [VarRule] [CleanVarRule],
	       count_vars CleanVarRule 1 N,
	       N1 is (N - 1),
	       extend_form_rule_rec CleanVarRule RuleSkel N1,
	       create_new_rr RuleSkel Rule N1,
	       env_otype Rule H _,
	       printstdout Rule
	       )
	      nil
	      Agenda.


atomic_critic general_critic roll_back_to_start
        Address
        Agenda
        (retrieve_node [] (and_node G [] C _ _ _),
         create_delete_list [] DeleteList,
         append DeleteList ((add_node [] (and_node G Ad C _ _ _))::nil) ChangeList)
        %% Putting the added node at the end since the deletelist will delete
        %% it first.
        (remove_from_agenda DeleteList Agenda NewAgenda,
         push_agenda [] NewAgenda AgendaOut)
        ChangeList
        AgendaOut.


local form_rule osyn -> osyn -> osyn -> o.
form_rule trueP LHS (app eq [LHS]):- !.
form_rule Cond LHS (app imp [Cond, (app eq [LHS])]).

local extend_form_rule osyn -> osyn -> int -> o.
extend_form_rule (app eq [LHS]) (app eq [LHS, (app F ArgList)]) N:- !,
		 create_arg_list N RArgList,
		 reverse RArgList ArgList.
extend_form_rule (app imp [Cond, (app eq [LHS])]) (app imp [Cond, (app eq [LHS, (app F ArgList)])]) N:-
		 create_arg_list N RArgList,
		 reverse RArgList ArgList.


local extend_form_rule_rec osyn -> osyn -> int -> o.
extend_form_rule_rec (app eq [(app Rfun Args)]) (app eq [(app Rfun Args), (app F ((app Rfun NewArgs)::ArgList))]) N:- !,
		 create_arg_list N RArgList,
		 reverse RArgList ArgList,
		 mappred Args (X\ Y\ sigma J\
			Y = (app J ArgList)) NewArgs.		  	
extend_form_rule_rec (app imp [Cond, (app eq [(app Rfun Args)])]) (app imp [Cond, (app eq [(app Rfun Args), (app F ((app Rfun NewArgs)::ArgList))])]) N:-
		 create_arg_list N RArgList,
		 reverse RArgList ArgList,
		 mappred Args (X\ Y\ sigma J\
			Y = (app J ArgList)) NewArgs.		  	

local create_arg_list int -> (list osyn) -> o.
create_arg_list 0 [].
create_arg_list N ((db N)::T):-
		N > 0,
		N1 is (N - 1),
		create_arg_list N1 T.

local count_vars osyn -> int -> int -> o.
count_vars (db N) N N1:- !,
	N1 is N + 1.
count_vars (db N) N1 N1.
count_vars X N N:-
	   obj_atom X.
count_vars (app F Args) Nin Nout:-
	   map_accum (F::Args) count_vars Nin Nout.
count_vars (abs X Type) Nin Nout:-
	   pi (x\ (count_vars (X x) Nin Nout)).

local create_new_rr osyn -> osyn -> int -> o.
create_new_rr Term Term 0.
create_new_rr TermIn (app forall [Type, (abs (x\ (TermOut x)) Type)])  N:-
	      N > 0,
	      pi x\ (replace_with TermIn (db N) x (TermOut1 x),
		     N1 is (N - 1),
		     create_new_rr (TermOut1 x) (TermOut x) N1).

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
		((not (Used = 0), 
                  poll_gb_tree Info GScore BScore, 
		  Score = [BScore, GScore]); 
                 Score = []))) Rules Scores,
		 not (Rules = []),
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
	  print "Bad Score:",
	  printstdout BS,
	  print "Good Score:",
	  printstdout GS,
            not(BS = 0), 
	    ((BS = MaxB, (GS = MaxG; GS < MaxG));
	     (BS > MaxB)), !, max_score TR TI [BS, GS] R RO);
	    max_score TR TI [MaxB, MaxG] RC RO).

/*
atomic_critic pdd_repair (sym_eval_critic 1 NewRule _)
	      Ad
	      Agenda
	      (get_goal Ad (seqGoal (H >>> G) C),
	       not (member (hyp _ new_rewrite) H))
	      (no_rule H G  C NewRule,
	       printstdout "WARNING: Missing Rewrite Rule",
	       printstdout NewRule)
	      nil
	      Agenda.
*/

compound induction (induction_top sym_eval_crit) (complete_meth
		(repeat_meth
		(orelse_meth trivials
		(orelse_meth allFi
	 	(orelse_meth taut
            	(orelse_meth (cond_meth contains_any_meta_var_goal fail_meth my_sym_eval)
		(orelse_meth (then_meth existential (try_meth my_sym_eval))
		(orelse_meth (repeat_meth generalisation_compound)
                         (ind_strat sym_eval_crit)
	))))))))
	_
	true.


compound rewriting my_sym_eval
	(repeat_meth 
	(then_meth (cond_meth contains_any_meta_var_goal (try_meth coerce_vars) id_meth)
	(orelse_meth rewrite_with_hyp
	(orelse_meth (orelse_meth
		(rewrite_with sym_eval_rewrites_list (R:rewrite_rule))
			(critic_meth sym_eval_crit_strat))
	(orelse_meth (then_meth rewrite_with_transitive_hyp (formula_tester [1,0] evaluate (label_truth _ 0 0)))
	(orelse_meth (rewrite_case_split sym_eval_rewrites_list (R1:rewrite_rule))
	(orelse_meth  redundant

	%% See if some "normalising" by moving implications can occur
	(orelse_meth (then_meth
		(then_meth (try_meth (repeat_meth all_i)) imp_i)
		(then_meth (try_meth (repeat_meth (orelse_meth and_e or_e)))
			(then_meth (repeat_meth rewrite_with_hyp) (formula_tester [3,0] evaluate (label_truth _ 0 0)))))
	
	(orelse_meth and_e or_e)))))))))
      Address
	true.

atomic pdd_repair stop_meth
       G
       true
       (printstdout "Stop Planning!!!!!")
       trueGoal
       notacticyet.

check_truth (app forall [Type, (abs Goal Type)]):-
		pi z\ (has_otype bound z Type => check_truth (Goal z)).
check_truth G :-
		known_false G.

no_rule Hyps (app forall [Type, (abs Goal Type)]) C NewRule:-
		pi z\ (has_otype bound z Type => no_rule Hyps (Goal z) C NewRule).
no_rule Hyps Goal C NewRule:-	
	no_rule_applies Goal,
	memb (unsure F _) C,
	subterm_of Goal (app F Args) _,
	nth Args N Arg Rest,
	type_constructor_test Arg,
	for_each Rest (A\ (not (subterm_of A (app F _) _))),
	mappred Args (Arg\ Type\ (env_otype Arg Hyps Type)) TypeList,
	construct_new_rule F N Args TypeList [] NewRule.
	

no_rule_applies Term:-
	sym_eval_rewrites_list List,
        (not (rewrite_with_rules List _ Term _ _)).

type_constructor_test S:-
	is_otype _ _ BaseConstructors StepConstructors,
	(member S BaseConstructors;
	member S StepConstructors).
type_constructor_test (app S _):-
	is_otype _ _ BaseConstructors StepConstructors,
	(member S BaseConstructors;
	member S StepConstructors).

local construct_new_rule osyn -> int -> list osyn -> list osyn -> list osyn -> osyn -> o.

construct_new_rule F _ [] [] L (app eq [(app F NewL), (app X NewL)]):-
	reverse L NewL.
construct_new_rule F 1 (H::L) (Type::TL) NewL NewRule:-
	construct_type_term Type H NewH,
	!, construct_new_rule F 0 L TL (NewH::NewL) NewRule.
construct_new_rule F N (H::L) (Type::TL) NewL (app forall [Type, (abs (x\ (NewRule x)) Type)]):-
	N1 is N - 1,
	pi x\ (construct_new_rule F N1 L TL (x::NewL) (NewRule x)).

local construct_type_term osyn -> osyn -> osyn -> o.
construct_type_term Type (app S Args) (app S NewList):-
	has_otype _ S (arrow List Type), !,
	length List N,
	length NewList N.
construct_type_term _ H H.
		


end
