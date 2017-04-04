module ripple_book.

accumulate clam_corpus.

local rbp osyn -> o.
rbp X.

%% Meta- Rippling

top_goal ripple_book meta_ripple []
	(app forall [nat, (abs (x\
		(app eq [(app even [x]),	
			 (app odd [(app s [x])])])) nat)]).

%% Simple Unblocking

lemma ripple_book ass_plus equiv
        trueP
        (app plus [(app plus [X, Y]), Z])
        (app plus [X, (app plus [Y, Z])]).

lemma ripple_book plus_lem equiv
	trueP
	(app plus [(app plus [A, B]), C])
	(app plus [(app plus [A, C]), B]).

lemma ripple_book cnc_plus equiv
	trueP
	(app eq [(app plus [X1, Y]), (app plus [X2, Y])])
	(app eq [X1, X2]).

top_goal ripple_book dist_unblock []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (y\ (app forall [nat,
      (abs (z\ (app eq [
       (app otimes [x, (app plus [y, z])]),
       (app plus [(app otimes [x, y]), (app otimes [x, z])])])) nat)])) nat)])) nat)]).

%% Dieter's example BBNotes 1204, 1205

has_otype ripple_book binom (arrow [nat, nat] nat).

definition ripple_book binom1
	trueP
	(app binom [X, zero])
	(app s [zero]).
definition ripple_book binom2
	trueP
	(app binom [zero, (app s [X])])
	zero.
definition ripple_book binom3
	trueP
	(app binom [(app s [X]), (app s [Y])])
	(app plus [(app binom [X, (app s [Y])]), (app binom [X, Y])]).

definition ripple_book minus1
        trueP
        (app minus  [X, zero])
        X.


lemma ripple_book minus_lem equiv
	trueP
	(app minus [(app s [X]), (app s [Y])])
	(app minus [X, Y]).
lemma ripple_book plus_r_lem equiv
      trueP
      (app plus [X, (app s [Y])])
      (app s [(app plus [X, Y])]).
lemma ripple_book plus_r_zero equiv
      trueP
      (app plus [X, zero])
      X.

top_goal ripple_book dieter_unblock []
	(app forall [nat,
		(abs (x\ 
	(app eq [(app minus [(app binom [x, (app s [zero])]), x]), zero])) nat)]).

%% sink cancellaton

has_otype ripple_book permute (arrow [(olist X), (olist X)] bool).
has_otype ripple_book del (arrow [X, (olist X)] (olist X)).

definition ripple_book permute1
	trueP
	(app permute [onil, onil])
	trueP.
definition ripple_book permute1
	trueP
	(app permute [onil, (app ocons [X, Y])])
	falseP.
definition ripple_book permute4
	(app omember [X, Z])
	(app permute [(app ocons [X, Y]), Z])
	(app permute [Y, (app del [X, Z])]).
definition ripple_book permute3
	(app neg [(app omember [X, Z])])
	(app permute [(app ocons [X, Y]), Z])
	falseP.

definition ripple_book del1
	trueP
	(app del [X, onil])
	onil.
definition ripple_book del2
	trueP
	(app del [X, (app ocons [X, Z])])
	Z.
definition ripple_book del3
	(app neq [X, H])
	(app del [X, (app ocons [H, Z])])
	(app ocons [H, (app del [X, Z])]).

top_goal ripple_book cancel_thm []
	(app forall [(olist nat),
		(abs (x\ (app permute [x, x])) (olist nat))]).

atomic ripple_book (wave_rpo Dir Rule)
	(seqGoal (Hyps >>> Goal) ((embedding_context E1 _)::T))
	(ripple_rewrite Hyps Rule (Goal @@ E1) (NewGoal @@ E2) Cond TermPos Dir T RDir,
	(trivial_condition Cond Hyps, 
	 (embeds_list E2 NewGoal E3 E1 E1p,
	 (measure_check Dir E3 E1p TermPos Embedding RDir,
	 (for_each_cut Embedding (E\ sinkable E nil))))))
        (log_rewrite_rule T Rule,
	 mappred Hyps (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce Hyps X Z;
		  Z = X)),
		 B = (hyp Z T))) NewHyps)
	(seqGoal (NewHyps >>> NewGoal) ((embedding_context Embedding Dir)::T))
	notacticyet.

ripple_operate wave_rpo_measure List NewList:-
	replace (wave_method outward R1) (wave_rpo outward R1) List NewList1,
	replace (wave_method inout T1) (wave_rpo inout T1) NewList1 NewList.

benchmark_plan ripple_book Meth Query :-
	testloop (
	(set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, s_functional, cons_functional, leq1, leq2, leq_ss, less1, less2, less3, neq_zero_s, neq_s_zero, and1, and2, and3, and4, neq_eq, imp1, imp2, imp3, ass_plus, cnc_plus, plus_lem, minus_lem, plus_r_lem, plus_r_zero],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list objlists,
        (add_theory_defs_to_sym_eval_list list_benchmarks,
        (add_theory_defs_to_sym_eval_list map_benchmarks,
        (add_theory_defs_to_sym_eval_list clam_corpus,
        (add_theory_defs_to_sym_eval_list ripple_book,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query)))))))))
        )).



end
