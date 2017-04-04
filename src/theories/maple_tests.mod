module maple_tests.

accumulate sums.

local difference_unify osyn -> osyn -> osyn -> o.

has_otype maple_tests div ((nat arrow nat) arrow bool).

definition maple_tests div1
	   trueP
	   (app div (tuple [A, B]))
	   (app exists (tuple [nat, 
	     (abs c\ (app eq (tuple [A, (app otimes (tuple [B, c]))])))])).

top_goal maple_tests q1 []
  (app forall (tuple [nat, (abs a\
    (app forall (tuple [nat, (abs b\
	(app forall (tuple [nat, (abs c\
  (app imp (tuple [
       (app and (tuple [
	    (app div (tuple [b, a])),
	    (app div (tuple [c, b]))])),
       (app div (tuple [c, a]))])))])))])))])).


atomic maple_tests exists_in_hyp 
    (seqGoal (H >>> G))
    (memb_and_rest (app exists (tuple [T, (abs x\ (P x))])) H NewH)
    true
    (allGoal T (x\ (seqGoal (((P x)::NewH) >>> G))))
    notacticyet.

compound maple_tests div_meth 
    (complete_meth
	(repeat_meth
		(orelse_meth sym_eval
		(orelse_meth existential
		(orelse_meth imp_i
		(orelse_meth all_i
		(orelse_meth exists_in_hyp
		(orelse_meth and_e
		eq_rewrite))))))))
   _
   true.

difference_unify A B C:-
		 headvar_osyn B,
		 headvar_osyn C, !.
difference_unify A B C:-
		 headvar_osyn B,
		 not (headvar_osyn C), !, fail.
difference_unify A B C:-
		 headvar_osyn C,
		 not (headvar_osyn B), !, fail.
difference_unify A A A:-
		 obj_atom A.
difference_unify (app K L) (app F L1) (app G L2):-
		 difference_unify K F G,
		 difference_unify L L1 L2, !.
difference_unify L (app F L1) T:-
		 difference_unify L L1 T.
difference_unify L T (app F L1):-
		 difference_unify L T L1.
difference_unify L (app F L1) T:-
		 difference_unify L F T.
difference_unify L T (app F L1):-
		 difference_unify L T F.
difference_unify (abs x\ (P x)) (abs y\ (Q y)) (abs z\ (R z)):-
		 pi x\ (difference_unify (P x) (Q x) (R x)), !.
difference_unify A (abs y\ (Q y)) B:-
		 pi x\ (difference_unify A (Q x) B).
difference_unify A B (abs y\ (Q y)):-
		 pi x\ (difference_unify A B (Q x)).

atomic maple_tests set_up_eq_ripple
       (seqGoal (H >>> (app eq (tuple [LHS, RHS]))))
       (difference_unify PSk LHS RHS,
        forthose EL (Emb\ Hin\ Skel\ (strip_forall_embeds Hin Emb Skel LHS)) (PSk::nil) Hwork,
        forthose ER (Emb\ Hin\ Skel\ (strip_forall_embeds Hin Emb Skel RHS)) (PSk::nil) Hwork,	
	(not (Hwork = nil)))
	true
	(eqripGoal (H >>> (app eq (tuple [LHS, RHS]))) Hwork EL ER)
	notacticyet.

atomic maple_tests post_eq_ripple
       (eqripGoal Seq _ _ _)
       true
       true
       (seqGoal Seq)
       notacticyet.

atomic maple_tests rippleL
       (eqripGoal (H >>> (app eq (tuple [LHS, RHS]))) Skel EL ER)
       (ripple_rewrite MKey Rule Skel (LHS @@ EL) (NewLHS @@ EL2) Cond TermPos,
        trivial_condition Cond Hyps,
	embeds_list EL2 Skel NewGoal Skel2 EL3 EL ELp,
	measure_check MKey Dir EL3 ELp TermPos Embedding Skel2 NewSkel)
	true
	(eqripGoal (H >>> (app eq (tuple [NewLHS, RHS]))) NewSkel Embedding ER)
	notacticyet.


atomic maple_tests rippleR
       (eqripGoal (H >>> (app eq (tuple [LHS, RHS]))) Skel EL ER)
       (ripple_rewrite MKey Rule Skel (RHS @@ ER) (NewRHS @@ ER2) Cond TermPos,
        trivial_condition Cond Hyps,
	embeds_list ER2 Skel NewGoal Skel2 ER3 ER ERp,
	measure_check MKey Dir ER3 ERp TermPos Embedding Skel2 NewSkel)
	true
	(eqripGoal (H >>> (app eq (tuple [LHS, NewRHS]))) NewSkel EL Embedding)
	notacticyet.

compound maple_tests eq_rewrite
	 (then_meth
		(repeat_meth fertilisation_weak)
		(then_meth set_up_eq_ripple
		(then_meth (repeat_meth (orelse_meth rippleL rippleR))
			   post_eq_ripple)))
	_
	true.


benchmark_plan maple_tests Meth Query:-
    testloop(set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list analytica,
        (set_sym_eval_list [div1],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list analytica,
        (set_wave_rule_to_sym_eval,
		pds_plan Meth Query)))))).                                  


end
