/*

File: challenges.mod
Author: Louise Dennis
Description: Induction workshop challenges

*/

module challenges.

accumulate list_benchmarks.

local challenges_dummy osyn -> o.
challenges_dummy X.

top_goal challenges iwc002 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [
		(app even [(app olength [(app oapp  [x, y])])]),
		(app even [(app olength [(app oapp  [y, x])])])])) (olist nat))])) (olist nat))]).

lemma challenges oapp_right rtol
	trueP
	(app olength [(app oapp  [X, (app ocons  [Y, Z])])])
	(app s [(app olength [(app oapp  [X, Z])])]).
lemma challenges oapp_right_onil rtol
	trueP
	(app olength [(app oapp  [X, onil])])
	(app olength [X]).


has_otype challenges split_list (arrow [(olist A), (olist A)] (olist A)).

definition challenges split_list1
	trueP
	(app split_list  [onil, W])
	W.
definition challenges split_list2
	(app eq  [(app olength [W]), (app s [(app s [(app s [(app s [(app s [(app s [zero])])])])])])])
	(app split_list  [(app ocons  [A, X]), W])
	(app ocons  [W, (app split_list  [(app ocons  [A, X]), onil])]).
definition challenges split_list3
	(app neq  [(app olength [W]), (app s [(app s [(app s [(app s [(app s [(app s [zero])])])])])])])
	(app split_list  [(app ocons  [A, X]), W])
	(app split_list  [X, (app oapp  [W, (app ocons  [A, onil])])]).

has_otype challenges new_split (arrow [(olist A), (olist A), nat] (olist A)).

definition challenges new_split1
	trueP
	(app new_split  [onil, W, D])
	W.
definition challenges new_split2
	(app eq  [D, (app s [(app s [(app s [(app s [(app s [(app s [zero])])])])])])])
	(app new_split  [(app ocons  [A, X]), W, D])
	(app ocons  [W, (app new_split  [(app ocons  [A, X]), onil, (app olength [onil])])]).
definition challenges new_split2
	(app neq  [D, (app s [(app s [(app s [(app s [(app s [(app s [zero])])])])])])])
	(app new_split  [(app ocons  [A, X]), W, D])
	(app new_split  [X, (app oapp  [W, (app ocons  [A, onil])]), (app s [D])]).


top_goal challenges iwc009_petes_nasty_theorem []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (w\
	(app eq  [
		(app new_split  [x, w, (app olength [w])]),
		(app split_list [x, w])])) (olist nat))])) (olist nat))]).

benchmark_plan challenges Meth Query :-
        testloop (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [oapp_right, oapp_right_onil, idty, s_functional, cons_functional, mono_fun_1, mono_fun_2],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list objlists,
        (add_theory_defs_to_sym_eval_list list_benchmarks,
        (add_theory_defs_to_sym_eval_list challenges,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query)))))))).


end
