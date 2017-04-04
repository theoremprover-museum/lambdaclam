/*

File: lim_plus.mod
Author: Louise Dennis
Description: Lim Plus example (for embeddings paper)

*/

module lim_plus.
accumulate arithmetic.
accumulate constructive_logic.

local dummylim_plus o -> o.
dummylim_plus X.
local dummylim_plus2 o -> o.
dummylim_plus2 X.
local dummylim_plus3 o -> o.
dummylim_plus3 X.

has_otype lim_plus lim (arrow [arrow [nat] nat, nat, nat] bool).
has_otype lim_plus less (arrow [nat, nat] bool).
has_otype lim_plus mod (arrow [nat] nat).

definition lim_plus lim1 
	trueP
	(app lim  [F, A, L])
	(app forall  [nat, (abs (epsilon\ 
	    (app imp  [
		(app less  [zero, epsilon]),  % Bool
		(app exists  [nat, (abs (delta\	
			(app and  [
				(app less  [zero, delta]), %Bool
		(app forall  [nat, (abs (x\
			(app imp  [
                            (app and  [
				(app neq  [x, A]),  %Bool
				(app less  [
					(app mod [(app minus  [x, A])]), 
					delta])]), %bool
			    (app less  [
				(app mod [
					(app minus  [(app F [x]), L])]), 
					epsilon])]) %Bool %Bool
		) nat)])])) nat)])])) nat)]).

lemma lim_plus minus_plus equiv
	trueP
	(app minus  [(app plus  [U1, U2]), (app plus  [V1, V2])])
	(app plus  [(app minus  [U1, V1]), (app minus  [U2, V2])]). 

lemma lim_plus mod_plus_less equiv
	trueP
	(app less  [(app mod [(app plus  [U, V])]), E])
	(app less  [(app plus  [(app mod [U]), (app mod [V])]), E]).

lemma lim_plus half_plus_less equiv
	trueP
	(app less  [(app plus  [U, V]), W])
	(app and  [(app less  [U, (app half [W])]), (app less  [V, (app half [W])])]).


lemma lim_plus forall_and ltor
	trueP
	(app forall  [A, (abs (x\
		(app and  [(app P1 [x]), (app P2 [x])])) A)])
	(app and  [(app forall  [A, (abs (x\	(app P1 [x])) A)]),
			 (app forall  [A, (abs (x\ (app P2 [x])) A)])]).

lemma lim_plus exists_less_and rtol
	trueP
	(app exists  [nat, (abs (delta\
		(app and  [(P delta),
	(app forall  [nat, (abs (x\
		(app imp  [(app and  [(C x),
			(app less  [(Q x), delta])]),
			(app and  [(R1 x), (R2 x)])])) nat)])])) nat)])
	(app and  [(app exists  [nat, (abs (delta\
		(app and  [(P delta),
	(app forall  [nat, (abs (x\
		(app imp  [(app and  [(C x),
			(app less  [(Q x), delta])]), (R1 x)])) nat)])])) nat)]),
	(app exists  [nat, (abs (delta\
		(app and  [(P delta),
	(app forall  [nat, (abs (x\
		(app imp  [(app and  [(C x),
			(app less  [(Q x), delta])]), (R2 x)])) nat)])])) nat)])]).	

lemma lim_plus less_half_and rtol
	trueP
	(app imp  [(app less  [zero, E]), (app and  [P, Q])])
	(app and  [(app imp  [(app less  [zero, (app half [E])]), P]), 
	           (app imp  [(app less  [zero, (app half [E])]), Q])]).	

top_goal lim_plus lim_plus_thm []
	(app forall  [arrow [nat] nat, (abs (f\
		(app forall  [arrow [nat] nat, (abs (g\
			(app forall  [nat, (abs (a\
				(app forall  [nat, (abs (l\
					(app forall  [nat, (abs (m\
	(app imp  [(app and  [(app lim  [f, a, l]),
			      (app lim  [g, a, m])]),
	(app lim  [(abs (x\
		(app plus  [(app f [x]), (app g [x])])) nat), a, 
                 (app plus  [l, m])])])) nat)])) nat)])) nat)])) 

	(arrow [nat] nat))])) (arrow [nat] nat))]).


top_goal lim_plus lim_minus_thm []
	(app forall  [arrow [nat] nat, (abs (f\
		(app forall  [arrow [nat] nat, (abs (g\
			(app forall  [nat, (abs (a\
				(app forall  [nat, (abs (l\
					(app forall  [nat, (abs (m\
	(app imp  [(app and  [(app lim  [f, a, l]),
					  (app lim  [g, a, m])]),
			 (app lim  [(abs (x\
		(app minus  [(app f [x]), (app g [x])])) nat), a, 
                      (app minus [l, m])])])) nat)])) nat)])) nat)])) 
                 (arrow [nat] nat))])) (arrow [nat] nat))]).


top_goal lim_plus testthm []
	(app or [falseP, falseP]).

compound induction lim_plus_meth (complete_meth
                (repeat_meth
                (orelse_meth (rewrite_with sym_eval_rewrites_list (R:rewrite_rule))
		(orelse_meth  (then_meth 
		                      (repeat_meth all_i)	
				      (then_meth
				      (repeat_meth (orelse_meth and_e imp_i))
				      (then_meth
		                      (repeat_meth all_i)	
			     (step_case lim_thm))))
                taut
        ))))
        _
        true.

atomic wave set_up_ripple_no_ind
         ( seqGoal (H >>> Goal) Context)
         ((%% Beta reduce the goal if necessary
               (congr (R\ P\ LHS\ RHS\ C\ 
               (rewr R P LHS RHS C)) beta_reduction positive_polarity Goal Goal2 _ _ _);
	   (Goal = Goal2)),

	   forthose E (Emb\ Hyp\ X\ (
		    strip_forall_embeds Hyp Emb Goal2)) H _,
	  (not (E = nil)), !,
	   not (member (embedding_context E outward) Context)
          )
          true
         (seqGoal (H >>> Goal2) ((embedding_context E outward)::Context) )
          notacticyet.

atomic induction fertilisation_strong
	( seqGoal (H >>> G) Context)
	(memb (hyp H1 _) H,
	 sink_match_ H1 G G2 H)  %jndw 2/12: modulo matching of sinks
	 (filter Context NewContext (H1\ (sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	 beta_reduce H G2 Gout,
	 mappred H (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce Hyps X Z;
		  Z = X)),
		 B = (hyp Z T))) NewHyps)
	(seqGoal (NewHyps >>> Gout) NewContext)
	notacticyet.

atomic induction fertilisation_weak
        ( seqGoal (H >>> (app eq [LHS, RHS]) ) Context)
        ( memb_and_rest (hyp Hyp _) H NewHyps,
          (rewrite_using Hyp LHS LHS1 red 0 Cond, RHS1 = RHS;
           rewrite_using Hyp RHS RHS1 nored 0 Cond, LHS1 = LHS),
	  trivial_condition Cond NewHyps
	)
	 (filter Context NewContext (H1\ (sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	 beta_reduce H (app eq [LHS1, RHS1]) Goal,
	 %% changed H to NewHyps in mappred
	 mappred NewHyps (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce H X Z);
		  Z = X),
		 B = (hyp Z T))) NH)
	( seqGoal ( NH >>> Goal ) NewContext)
        notacticyet.

atomic induction fertilisation_weak
        ( seqGoal (H >>> G ) Context)
        ( memb_and_rest (hyp Hyp _) H NewHyps,
          (rewrite_using Hyp G G1 _ 1 Cond;
           rewrite_using_transitive Hyp G G1 _ 1 Cond),
	  trivial_condition Cond NewHyps
	)
	 (filter Context NewContext (H1\ (sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	 beta_reduce H G1 G2,
	 mappred H (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce Hyps X Z;
		  Z = X)),
		 B = (hyp Z T))) NH)
	( seqGoal ( NHs >>> G2 ) NewContext)
        notacticyet.


control_rule_for induction (ripple_set_up lim_thm) _ List NewList:-
	prefer [set_up_ripple] List NewList1,
	reject [all_i, existential] NewList1 NewList2,
	replace set_up_ripple set_up_ripple_no_ind NewList2 NewList3,
	ripple_operate with_critics NewList3 NewList.

ripple_operate lim_thm A B:-
	reject [fertilise] A A1,
	ripple_operate with_critics A1 B.

benchmark_plan lim_plus Meth Query :-
        testloop 
        (% interaction_mode open_math,
	(set_sym_eval_list [idty, s_functional, lim1, beta_reduction],
        (add_theory_defs_to_sym_eval_list arithmetic,
	(set_wave_rule_list [idty, s_functional, minus_plus, mod_plus_less, half_plus_less, forall_and, exists_less_and, less_half_and],
	(add_theory_defs_to_wave_rule_list arithmetic,
        pds_plan Meth Query))))).


end
