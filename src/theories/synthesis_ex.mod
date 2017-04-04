/*

File: synthesis_ex.mod
Author: Louise Dennis

Description:  Synthesis Example from Smail and Green, Higher-Order Annotated Terms for Proof Search.

*/

module synthesis_ex.
accumulate list_benchmarks.

local syndummy o -> o.
syndummy X.

top_goal synthesis_ex synthesis_thm []
	(app forall  [(olist nat), (abs m\
		(app forall  [(olist nat), (abs l\
			(app exists  [(olist nat), (abs n\
				(app forall  [nat, (abs x\
	(app imp  [(app or  [(app omember  [x, m]),
					(app omember  [x, l])]),
			 (app omember  [x, n])]))]))]))]))]).

definition synthesis_ex omem4
	trueP
	(app omember  [X, (app ocons  [H, T])])
	(app or  [(app eq  [X, H]), (app omember  [X, T])]).

lemma synthesis_ex ass_or equiv
	trueP
	(app or  [(app or  [P, Q]), R])
	(app or  [P, (app or  [Q, R])]).

lemma synthesis_ex prop1 rtol trueP (app imp  [(app or  [X, Y]), 
                                     (app or  [X, Z])])
                           (app imp [Y, Z]).

benchmark_plan synthesis_ex Meth Query :-
        testloop (%interaction_mode command,
	(%plan_printing on,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, cons_functional, or3],
        (add_to_sym_eval_list [omem1, omem4, prop1],
        (set_wave_rule_to_sym_eval,
	(add_to_wave_rule_list [ass_or],
        pds_plan Meth Query)))))))).

compound synthesis_ex (induction_top exi) (complete_meth
		(repeat_meth
		(orelse_meth trivial
		(orelse_meth allFi
	 	(orelse_meth taut
            	(orelse_meth sym_eval
		(orelse_meth (repeat_meth generalise)
                         (ind_strat exi)
	)))))))
	_
	true.

atomic synthesis_ex (set_up_ex_ripple N)
         ( seqGoal (H >>> Goal) Context)
         ( induction_hypothesis H H1 _, 
	  forthose E (Emb\ H\ X\ (strip_forall_embeds H Emb Goal)) H1 _,
	  (not (E = nil)), !
	 )
	true
         (seqGoal (H >>> Goal) [(embedding_context E outward), (int_context N)] )
          notacticyet.

%% Allow a measure increasing step but reduce the maximum allowable such steps.
atomic synthesis_ex (ex_wave_method Dir Rule)
	(seqGoal (Hyps >>> Goal) ((embedding_context E1 _)::((int_context N)::T)))
	(N > 0,
	 ripple_rewrite Hyps Rule (Goal @@ E1) (NewGoal @@ E2) Cond TermPos,
	definition _ Rule _ _ _,
	(trivial_condition Cond Hyps,
	 (embeds_list E2 NewGoal E3 E1 E1p,
	 (not (measure_check Dir E3 E1p TermPos _ )),
	 (for_each_cut E3 sinkable),
	 N1 is (N - 1))))
	true
	(seqGoal (Hyps >>> NewGoal) ((embedding_context E3 Dir)::((int_context N1)::T)))
	notacticyet.

compound synthesis_ex (step_case exi)
        ( cut_meth
	(then_meth
           ( then_meth (try_meth (repeat_meth (orelse_meth all_i existential))) (set_up_ex_ripple 1))

	(then_meth 
	
	(orelse_meth
	(then_meth
	   (repeat_meth (ex_wave_method outward R))
		(then_meth
	   (repeat_meth (wave_method outward R))
	      (orelse_meth (repeat_meth fertilisation_strong)
		(then_meth	
		   (try_meth (repeat_meth 
                      (wave_method inout R1) ))
		   (try_meth fertilise)
		)
	      ))
	)
	
	
	(then_meth	
	   (repeat_meth 
              (wave_method inout R1))
	   fertilise
	))
	

	(then_meth post_ripple (then_meth
		(then_meth (try_meth sym_eval) (try_meth fertilise))
		(try_meth (repeat_meth all_e))))
		
	)))
	_
	true.



end
