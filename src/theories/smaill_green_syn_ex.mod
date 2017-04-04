/*

File: smaill_green_syn_ex.mod
Author: Louise Dennis

Description:  Synthesis Example from Smail and Green, Higher-Order Annotated Terms for Proof Search.

*/

module smaill_green_syn_ex.
accumulate clam_corpus.

local contains_meta_var (list int) -> osyn -> o.

/*
local syndummy o -> o.
syndummy X.
local syndummy2 o -> o.
syndummy2 X.
local syndummy3 o -> o.
syndummy3 X.
local syndummy4 o -> o.
syndummy4 X:-
	  printstdout X.
*/

top_goal smaill_green_syn_ex synthesis_thm []
	(app forall  [(olist nat), (abs (m\
		(app forall  [(olist nat), (abs (l\
			(app exists  [(olist nat), (abs (n\
				(app forall  [nat, (abs (x\
	(app imp  [(app or  [(app omember  [x, m]),
					(app omember  [x, l])]),
			 (app omember  [x, n])])) nat)])) (olist nat))])) (olist nat))])) (olist nat))]).

top_goal smaill_green_syn_ex sqr []
	(app forall  [nat, (abs (x\
		(app exists  [nat, (abs (y\
	(app and  [(app leq  [(app otimes  [y, y]), x]),
			 (app less  [x, (app otimes  [
					(app s [y]),
					(app s [y])])])])) nat)])) nat)]).

top_goal smaill_green_syn_ex tcons []
	(app forall  [nat, (abs (a\
		(app forall  [(olist nat), (abs (l\
			(app exists  [(olist nat), (abs (x\
	(app eq  [x, (app oapp  [l, (app ocons  [a,  onil])])])) (olist nat))])) (olist nat))])) nat)]).

top_goal smaill_green_syn_ex sg_cons []
	 (app forall  [(olist nat), (abs (l\
	      (app forall  [nat, (abs (a\
		   (app exists  [(olist nat), (abs (m\
			(app forall  [nat, (abs (x\
         (app imp  [
	      (app or  [(app eq  [x, a]), (app omember  [x, l])]),
	      (app omember  [x, m])])) nat)])) (olist nat))])) nat)])) (olist nat))]).

top_goal smaill_green_syn_ex sg_app []
	 (app forall  [(olist nat), (abs (x\
	      (app forall  [(olist nat), (abs (y\
		   (app exists  [(olist nat), (abs (z\
			(app forall  [nat, (abs (e\
         (app imp  [
	      (app or  [(app omember  [e, x]), (app omember  [e, y])]),
	      (app omember  [e, z])])) nat)])) (olist nat))])) (olist nat))])) (olist nat))]).

top_goal smaill_green_syn_ex sg_syn4 []
	 (app forall  [(olist nat), (abs (x\
	      (app forall  [(olist nat), (abs (y\
		   (app exists  [(olist nat), (abs (z\
			(app forall  [nat, (abs (e\
         (app imp  [
	      (app and  [(app omember  [e, x]), (app omember  [e, y])]),
	      (app omember  [e, z])])) nat)])) (olist nat))])) (olist nat))])) (olist nat))]).

top_goal smaill_green_syn_ex sg_pair []
	 (app forall  [nat, (abs (x\
	      (app forall  [nat, (abs (y\
		   (app exists  [(olist nat), (abs (z\
			(app forall  [nat, (abs (e\
         (app imp  [
	      (app or  [(app eq  [e, x]), (app eq  [e, y])]),
	      (app omember  [e, z])])) nat)])) (olist nat))])) nat)])) nat)]).

top_goal smaill_green_syn_ex sg_asps []
	 (app forall  [nat, (abs (x\
	      (app forall  [nat, (abs (y\
		   (app forall  [nat, (abs (z\
			(app exists  [nat, (abs (w\
	(app eq  [(app plus  [x, w]), 
		        (app plus  [(app plus  [x, y]), z])])) nat)])) nat)])) nat)])) nat)]).

top_goal smaill_green_syn_ex sg_pair2 []
	 (app forall  [nat, (abs (x\
	      (app forall  [nat, (abs (y\
		   (app exists  [(olist nat), (abs (z\
		   (app and  [
			(app forall  [nat, (abs (e\
         (app iff  [
	      (app or  [(app eq  [e, x]), (app eq  [e, y])]),
	      (app omember  [e, z])])) nat)]), (app ordered [z])])) (olist nat))])) nat)])) nat)]).

top_goal smaill_green_syn_ex sg_half []
	 (app forall  [nat, (abs (x\
	      (app exists  [nat, (abs (y\
	 (app or  [(app eq  [x, (app double [y])]),
			 (app eq  [x, (app s [(app double [y])])])])) nat)])) nat)]).

top_goal smaill_green_syn_ex sg_even []
	 (app forall  [nat, (abs (x\
	 (app or  [
	      (app exists  [nat, (abs (y\
		   (app eq  [x, (app double [y])])) nat)]),
	      (app exists  [nat, (abs (y\
			 (app eq  [x, (app s [(app double [y])])])) nat)])])) nat)]).

definition smaill_green_syn_ex omem4
	trueP
	(app omember  [X, (app ocons  [H, T])])
	(app or  [(app eq  [X, H]), (app omember  [X, T])]).

lemma smaill_green_syn_ex ass_or equiv
	trueP
	(app or  [(app or  [P, Q]), R])
	(app or  [P, (app or  [Q, R])]).

lemma smaill_green_syn_ex prop1 equiv trueP (app imp  [(app or  [X, Y]), 
                                     (app or  [X, Z])])
                           (app imp  [Y, Z]).

lemma smaill_green_syn_ex singleton equiv
      trueP
      (app omember  [P, (app ocons  [P, onil])])
      trueP.

lemma smaill_green_syn_ex exists_or_l equiv
      trueP
      (app or [(app exists [Type, (abs (x\ (E x)) Type)]), B])
      (app exists [Type, (abs (x\ (app or [(E x), B])) Type)]).

lemma smaill_green_syn_ex exists_or_r equiv
      trueP
      (app or [A, (app exists [Type, (abs (x\ (E x)) Type)])])
      (app exists [Type, (abs (x\ (app or [A, (E x)])) Type)]).

benchmark_plan smaill_green_syn_ex Meth Query :-
        testloop (%interaction_mode command,
	(%plan_printing on,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, neq_zero_s, neq_s_zero, cons_functional, mono_fun_1, mono_fun_2, or3, or4, s_functional, singleton],
        (add_theory_defs_to_sym_eval_list arithmetic,
	(delete_from_sym_eval_list [fun_iter1, fun_iter2, fun_iter3],
        (add_theory_defs_to_sym_eval_list objlists,
        (add_to_sym_eval_list [omem1, omem4, prop1, exists_or_l, exists_or_r],
        (set_wave_rule_to_sym_eval,
	(add_to_wave_rule_list [ass_or],
        pds_plan Meth Query))))))))))
%% )
).

atomic smaill_green_syn_ex (set_up_ex_ripple N)
         ( seqGoal (H >>> Goal) Context)
         ( induction_hypothesis H H1 _, 
	   not (member (embedding_context _ outward) Context),
	findall (Emb\ (sigma Hin\ (memb Hin H1, strip_forall_embeds Hin Emb Goal))) E,
	  (not (E = nil)), 
	   not (member (embedding_context E outward) Context),
	!
	 )
	true
         (seqGoal (H >>> Goal) ((embedding_context E outward)::((int_context N)::Context)) )
          notacticyet.
 

%% Allow a measure increasing step but reduce the maximum allowable such steps.
atomic smaill_green_syn_ex (ex_wave_method Dir Rule)
	(seqGoal (Hyps >>> Goal) ((embedding_context E1 _)::((int_context N)::T)))
	(ripple_rewrite Hyps Rule (Goal @@ E1) (NewGoal @@ E2) Cond TermPos Dir T RDir, 
	(trivial_condition Cond Hyps,
	((N > 0, mappred E2 (modify_new_emb Goal) E2p); E2 = E2p),
%%	E2 = E2p,
	 (embeds_list E2p NewGoal E3 E1 E1p,
	 ((%(measure_check Dir E3 E1p TermPos Embedding 2,
	%	N1 = N);
	  (N > 0, not (measure_check Dir E3 E1p TermPos Embedding 2), 
	   reverse TermPos RTermPos,
	   contains_meta_var RTermPos Goal,
	   definition _ Rule _ _ _, 
           N1 is N - 1,
           mappred E3 fix_out Embedding)), 
	 (for_each_cut Embedding (E\ sinkable E nil))))))
	true
	(seqGoal (Hyps >>> NewGoal) ((embedding_context Embedding Dir)::((int_context N1)::T)))
	notacticyet.
change_method_vars (ex_wave_method Dir Rule) (ex_wave_method Dir _) :- !.

local modify_new_emb osyn -> etree -> etree -> o.
modify_new_emb G (leaf Dir Pos Osyn) (leaf Dir _ Osyn):-
	       (not (Pos = []); not (Pos = [1])),
	       subterm_of G Os Pos,
	       contains_meta_var_term Os, !.
modify_new_emb _ (leaf Dir Pos Osyn) (leaf Dir Pos Osyn).
modify_new_emb G (sink Dir Pos Osyn) (sink Dir _ Osyn):-
	       (not (Pos = []); not (Pos = [1])),
	       subterm_of G Os Pos,
	   contains_meta_var_term Os, !.
modify_new_emb _ (sink Dir Pos Osyn) (sink Dir Pos Osyn).
modify_new_emb G (node Dir Pos F FL) (node Dir Pos1 F1 FL1):-
	   mappred (F::FL) (modify_new_emb G) (F1::FL1).
modify_new_emb G (absnode E) (absnode E1):-
	   pi x\ (modify_new_emb G (E x) (E1 x)).


local fix_out etree -> etree -> o.
fix_out (node outward Pos F FL) (node outward Pos F1 FL1):-
	!, mappred (F::FL) fix_out (F1::FL1).
fix_out (node Dir Pos F FL) (node Dir Pos F1 FL1):-
	!, mappred (F::FL) fix_out (F1::FL1).
fix_out (absnode E) (absnode E1):-
	pi x\ (fix_out (E x) (E1 x)).
fix_out (leaf outward Pos Osyn) (leaf outward Pos Osyn):-!.
fix_out (leaf Dir Pos Osyn) (leaf Dir Pos Osyn).
fix_out (sink outward Pos Osyn) (sink outward Pos Osyn):-!.
fix_out (sink Dir Pos Osyn) (sink Dir Pos Osyn).

ripple_operate exi List (or_fert::NewList):-
	replace (wave_method outward R1) (orelse_meth (wave_method outward R1) (ex_wave_method outward R1)) List NewList1,
	replace (wave_method inout T1) (orelse_meth (wave_method inout T1) (ex_wave_method inout T1)) NewList1 NewList2,
	replace (set_up_ripple) (set_up_ex_ripple 1) NewList2 NewList.

/*
compound smaill_green_syn_ex (step_case exi)
        ( cut_meth
        (then_meth
           ( then_meth (try_meth (repeat_meth (orelse_meth all_i existential))) (set_up_ex_ripple 1))
 
        (then_meth
         
        (orelse_meth
        (then_meth
           (repeat_meth (ex_wave_method outward R))
              (orelse_meth (repeat_meth fertilisation_strong)
                (then_meth
                   (try_meth (repeat_meth
                      (ex_wave_method inout R1) ))
                   (try_meth fertilise)
                )
              ))
                                                                                   
                                                                                   
        (then_meth
           (repeat_meth
              (ex_wave_method inout R1))
           fertilise
        ))
                                                                                                                                    
        (then_meth post_ripple (then_meth
                (then_meth (try_meth sym_eval) (try_meth fertilise))
                (try_meth (repeat_meth all_e))))
                                                                                   
        )))
        _
        true.
*/                                                                                   
contains_meta_var (1::TermPos) (app Rator _):-
		  contains_meta_var TermPos Rator.
contains_meta_var (N::TermPos) (app _ Rand):-
		  N > 1,
		  N1 is (N - 1),
		  nth Rand N1 Term _,
		  contains_meta_var TermPos Term.
contains_meta_var TermPos (abs Term Type):-
		  pi (x\ ((has_otype smaill_green_syn_ex x Type) => (contains_meta_var TermPos (Term x)))).
contains_meta_var nil Term:-
		  contains_meta_var_term Term.



end
