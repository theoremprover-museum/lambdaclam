/*

File: clam_corpus3.mod
Author: Louise Dennis
Description:  Clam theorems for benchmarking.
Last Modified: 28th May 2001

*/

module clam_corpus3.

accumulate list_benchmarks.

local dummypredicate osyn -> o.
dummypredicate X.
local cc3 osyn -> o.
cc3 X.
local cc3a osyn -> o.
cc3a X.

has_otype clam_corpus3 binom (arrow [nat, nat] nat).
has_otype clam_corpus3 minus (arrow [nat, nat] nat).

definition clam_corpus3 binom1
	trueP
	(app binom  [X, zero])
	(app s [zero]).
definition clam_corpus3 binom2
	trueP
	(app binom  [zero, (app s [PY])])
	zero.
definition clam_corpus3 binom3
	trueP
	(app binom  [(app s [PX]), (app s [PY])])
	(app plus  [(app binom  [PX, (app s [PY])]), 
                          (app binom  [PX, PY])]).

definition clam_corpus3 minus1
	trueP
	(app minus  [X, zero])
	X.
definition clam_corpus3 minus2
	trueP
	(app minus  [X, (app s [Y])])
	(app pred [(app minus  [X, Y])]).


top_goal clam_corpus3 binom_one []
	(app forall  [nat, (abs (x\
		(app eq  [
                    (app minus  [(app binom  [x, (app s [zero])]), 
                                       x]), 
                    zero])) nat)]).

top_goal clam_corpus3 minus_plus []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app eq  [(app minus  [(app plus  [z, x]),
					   (app plus  [z, y])]),
			(app minus  [x, y])])) nat)])) nat)])) nat)]).

top_goal clam_corpus3 minus_pred []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app eq  [(app pred [(app minus  [x, y])]),
			(app minus  [(app pred [x]), y])])) nat)])) nat)]).

top_goal clam_corpus3 minus_succ []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app eq  [(app minus  [x, y]),
			(app minus  [(app s [x]), (app s [y])])])) nat)])) nat)]).

benchmark_plan clam_corpus3 Meth Query :-
        testloop (interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list objlists,
        (add_theory_defs_to_sym_eval_list list_benchmarks,
        (add_theory_defs_to_sym_eval_list map_benchmarks,
        (add_theory_defs_to_sym_eval_list clam_corpus3,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query))))))))
        )).
end
