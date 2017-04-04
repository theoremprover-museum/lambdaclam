/*

File: clam_corpus2.mod
Author: Louise Dennis
Description:  Clam theorems for benchmarking.
Last Modified: 28th May 2001

*/

module clam_corpus2.

accumulate list_benchmarks.

%% Predicate to get thing to compile

/*
local cc_pred osyn -> o.
cc_pred X.
local cc2 osyn -> o.
cc2 X.
*/
local cc3 osyn -> o.
cc3 X.

has_otype clam_corpus2 prod (arrow [(olist nat)] nat).
definition clam_corpus2 prod1
	trueP
	(app prod [onil])
	(app s [zero]).
definition clam_corpus2 prod2
	trueP
	(app prod [(app ocons [H, T])])
	(app otimes [H, (app prod [T])]).

has_otype clam_corpus2 last (arrow [(olist X)] (olist X)).
definition clam_corpus2 last1
	trueP 
	(app last [onil])
	onil.
definition clam_corpus2 last2
	trueP
	(app last [(app ocons  [H, onil])])
	(app ocons  [H, onil]).
definition clam_corpus2 last3
	trueP
	(app last [(app ocons  [H, (app ocons  [H2, T])])])
	(app last [(app ocons  [H2, T])]).

has_otype clam_corpus2 fac (arrow [nat] nat).
definition clam_corpus2 fac1
	trueP
	(app fac [zero])
	(app s [zero]).
definition clam_corpus2 fac2
	trueP
	(app fac [(app s [N])])
	(app otimes  [(app s [N]), (app fac [N])]).

lemma clam_corpus2 times_less ltor 
      trueP
      (app and  [(app less  [zero, X]), (app less  [zero, Y])])
      (app less  [zero, (app otimes  [X, Y])]).

top_goal clam_corpus2 fac_less []
	(app forall  [nat, (abs (x\
	(app less  [zero, (app fac [x])])) nat)]).

top_goal clam_corpus2 cnc_pl1 []
	(app forall  [nat, (abs (u1\
		(app forall  [nat, (abs (u2\
			(app forall  [nat, (abs (v\
	(app imp  [(app eq  [u1, u2]),
			 (app eq  [(app plus  [v, u1]),
					 (app plus  [v, u2])])])) nat)])) nat)])) nat)]).

top_goal clam_corpus2 cnc_s []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app eq  [x, y]),
			 (app eq  [(app s [x]), (app s [y])])])) nat)])) nat)]).

%% Clam allows times2right as a rewrite rule
top_goal clam_corpus2 commthree []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app eq  [(app otimes  [(app otimes  [z, x]), y]),
			(app otimes  [(app otimes  [z, y]), x])])) nat)])) nat)])) nat)]).

top_goal clam_corpus2 comp2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app eq  [(app plus  [x, (app plus  [y, z])]),
			(app plus  [y, (app plus  [x, z])])])) nat)])) nat)])) nat)]).

top_goal clam_corpus2 dedthm []
	(app forall  [bool, (abs (p\
		(app forall  [bool, (abs (q\
			(app forall  [bool, (abs (r\
	(app imp  [(app imp  [p, (app imp  [q, r])]),
			 (app imp  [(app and  [p, q]), r])])) bool)])) bool)])) bool)]).




top_goal clam_corpus2 evendouble []
	(app forall  [nat, (abs (n\
		(app even [(app double [n])])) nat)]).

top_goal clam_corpus2 evenm []
	(app forall  [nat, (abs (n\
		(app forall  [nat, (abs (m\
	(app imp  [(app even [n]),
			 (app even [(app otimes  [n, m])])])) nat)])) nat)]).

top_goal clam_corpus2 evenp []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app and  [(app even [x]), (app even [y])]),
			 (app even [(app plus  [x, y])])])) nat)])) nat)]).

top_goal clam_corpus2 identrm []
	(app forall  [nat, (abs (x\
		(app eq  [(app otimes  [x, (app s [zero])]), x])) nat)]).

top_goal clam_corpus2 leqdouble []
	(app forall  [nat, (abs (x\
		(app leq  [x, (app double [x])])) nat)]).

top_goal clam_corpus2 leqdupl []
	(app forall  [nat, (abs (a\
		(app forall  [nat, (abs (b\
	(app or  [(app leq  [a, b]), (app leq  [b, a])])) nat)])) nat)]).


top_goal clam_corpus2 leqhalf []
	(app forall  [nat, (abs (x\
		(app leq  [(app half [x]), x])) nat)]).

top_goal clam_corpus2 leqhalfdouble []
	(app forall  [nat, (abs (x\
		(app leq  [(app half [x]), (app double [x])])) nat)]).

top_goal clam_corpus2 foldapp []
	(app forall  [(olist nat), (abs (a\
		(app forall  [(olist nat), (abs (b\
			(app forall  [(olist nat), (abs (c\
				(app forall  [arrow [nat, (olist nat)] (olist nat), (abs (f\
	(app eq  [(app foldr  [f, (app oapp  [a, b]), c]),
			(app foldr  [f, a, (app foldr  [f, b, c])])])) (arrow [nat, (olist nat)] (olist nat)))])) (olist nat))])) (olist nat))])) (olist nat))]).

%% Failes because of universally quantified hypothesis
top_goal clam_corpus2 multzero []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app eq  [(app otimes  [x, (app otimes  [y, zero])]),
			(app otimes  [y, (app otimes  [z, zero])])])) nat)])) nat)])) nat)]).

top_goal clam_corpus2 plus1right []
	(app forall  [nat, (abs (x\
		(app eq  [(app plus  [x, zero]),
				x])) nat)]).
top_goal clam_corpus2 qrev_correct_gen []
	(app forall  [(olist nat), (abs (l\
		(app forall  [(olist nat), (abs (m\
	(app eq  [(app qrev  [l, m]),
			(app oapp  [(app orev [l]), m])])) (olist nat))])) (olist nat))]).
top_goal clam_corpus2 orevmapcar []
	(app forall  [arrow [nat] nat, (abs (f\
		(app forall  [(olist nat), (abs (l\
	(app eq  [(app orev [(app mapcar  [f, l])]),
			(app mapcar  [f, (app orev [l])])])) (olist nat))])) (arrow [nat] nat))]).

top_goal clam_corpus2 times1right []
	(app forall  [nat, (abs (x\
		(app eq  [(app otimes  [x, zero]), zero])) nat)]).

top_goal clam_corpus2 zerotimes1 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app eq  [x, zero]),
			 (app eq  [(app otimes  [x, y]), zero])])) nat)])) nat)]).

top_goal clam_corpus2 zerotimes2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app eq  [y, zero]),
			 (app eq  [(app otimes  [x, y]), zero])])) nat)])) nat)]).

%% Not in my version of clam
top_goal clam_corpus2 zerotimes3 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app eq  [(app otimes  [x, y]), zero]),
			 (app or  [
				(app eq  [x, zero]),
				(app eq  [y, zero])])])) nat)])) nat)]).

top_goal clam_corpus2 cnc_last []
	(app forall  [nat, (abs (h\
		(app forall  [(olist nat), (abs (t1\
			(app forall  [(olist nat), (abs (t2\
	(app imp  [(app eq  [t1, t2]),
		 	 (app eq  [(app last [(app ocons [h, t1])]),
					 (app last [(app ocons  [h, t2])])])])) (olist nat))])) (olist nat))])) nat)]).

% "needs normalise"
top_goal clam_corpus2 prod_times []
	(app forall  [nat, (abs (u\
		(app forall  [(olist nat), (abs (v\
			(app forall  [nat, (abs (w\
	(app imp  [(app eq  [(app prod [v]), w]),
			 (app eq  [(app prod [(app ocons  [u, v])]),
					 (app otimes  [u, w])])])) nat)])) (olist nat))])) nat)]).


top_goal clam_corpus2 prodl [] 
        (app forall  [(olist nat), 
            (abs (l\ (app forall  [(olist nat), 
            (abs (m\ (app eq [(app prod  [(app oapp  [l, m])]), 
                             (app otimes  [(app prod [l]), (app prod [m])])])) (olist nat))])) (olist nat))]).

% "needs normalise"
top_goal clam_corpus2 prodlwave [] 
        (app forall  [nat, (abs (w\ 
        (app forall  [nat, (abs (v\ 
        (app forall  [(olist nat), (abs (w1\ 
        (app forall  [(olist nat), (abs (v1\ 
        (app imp  [(app and  [(app eq  [(app prod [w1]), w]), 
                              (app eq  [(app prod [v1]), v])]), 
                   (app eq  [(app prod [(app oapp  [w1, v1])]), (app otimes [w, v])])])) (olist nat))])) (olist nat))])) nat)])) nat)]).

benchmark_plan clam_corpus2 Meth Query :-
        testloop (%interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2, leq1, leq2, leq_ss, times_less, less1, less2, less3, neq_s_zero, neq_zero_s],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list objlists,
        (add_theory_defs_to_sym_eval_list list_benchmarks,
        (add_theory_defs_to_sym_eval_list map_benchmarks,
        (add_theory_defs_to_sym_eval_list clam_corpus2,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query))))))))
        )).

end
