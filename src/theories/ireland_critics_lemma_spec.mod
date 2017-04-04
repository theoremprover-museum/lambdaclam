/* 

File: ireland_critics.mod
Author: Louise Dennis
Description: Examples taken from Productive Use of Failure in
Inductive Proof by Andrew and Alan B.  These are the example problems
on which clam 3 was tested.
Created: 21st May 2002

*/

module ireland_critics_lemma_spec.

accumulate clam_corpus.

local icdummy osyn -> o.
icdummy X.

/*

icT1 == doubleplus
icT2 == comapp

*/

top_goal ireland_critics_lemma_spec icT3 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app olength [(app oapp  [x, y])]),
			(app plus  [(app olength [y]), (app olength [x])])])) (olist nat))])) (olist nat))]).

/*

icT4 == lendouble
icT5 == lenorev

*/

top_goal ireland_critics_lemma_spec icT6 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app olength [(app orev [(app oapp  [x, y])])]),
			(app plus  [(app olength [x]), (app olength [y])])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT7 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app olength [(app qrev  [x, y])]),
			(app plus  [(app olength [x]), (app olength [y])])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT8 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [(olist nat), (abs (z\
	(app eq  [(app drop  [x, (app drop  [y, z])]),
			(app drop  [y, (app drop  [x, z])])])) (olist nat))])) (olist nat))])) nat)]).

top_goal ireland_critics_lemma_spec icT9 []
	(app forall  [nat, (abs (w\
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app eq  [(app drop  [w, (app drop  [x, (app drop  [y, z])])]),
			(app drop  [y, (app drop  [x, (app drop  [w, z])])])])) nat)])) nat)])) nat)])) nat)]).

/* icT10 == orevorev */

top_goal ireland_critics_lemma_spec icT11 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app orev [(app oapp  [(app orev [x]), (app orev [y])])]),
			(app oapp  [y, x])])) (olist nat))])) (olist nat))]).

/*

icT12 == qrev_correct_gen 
icT13 == halfplus

*/

top_goal ireland_critics_lemma_spec icT14 []
	(app forall  [(olist nat), (abs (x\
		(app ordered [(app sort [x])])) (olist nat))]).

/*

icT15 == plus1right

*/

top_goal ireland_critics_lemma_spec icT16 []
	(app forall  [nat, (abs (x\
		(app even [(app plus  [x, x])])) nat)]).


top_goal ireland_critics_lemma_spec icT17 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app orev [(app orev [(app oapp  [x, y])])]),
			(app orev [(app oapp  [(app orev [y]), (app orev [x])])])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT18 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app orev [(app oapp  [(app orev [x]), y])]),
			(app oapp  [(app orev [y]), x])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT19 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app oapp  [(app orev [(app orev [x])]), (app orev [y])]),
			(app orev [(app orev [(app oapp  [x, y])])])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT20 []	
	(app forall  [(olist nat), (abs (x\
		(app even [(app olength [(app oapp  [x, x])])])) (olist nat))]).

/* icT21 == rotlen */

top_goal ireland_critics_lemma_spec icT22 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app even [(app olength [(app oapp  [x, y])])]),
			(app even [(app olength [(app oapp  [y, x])])])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT23 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app half [(app olength [(app oapp  [x, y])])]),
			(app half [(app olength [(app oapp  [y, x])])])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT24 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app eq  [(app even [(app plus  [x, y])]),
			(app even [(app plus  [y, x])])])) nat)])) nat)]).

top_goal ireland_critics_lemma_spec icT25 []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app eq  [(app even [(app olength [(app oapp  [x, y])])]),
			(app even [(app plus  [(app olength [x]), (app olength [y])])])])) (olist nat))])) (olist nat))]).

top_goal ireland_critics_lemma_spec icT26 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app eq  [(app half [(app plus  [x, y])]),
			(app half [(app plus  [y, x])])])) nat)])) nat)]).

/* icT36 = memapp
icT37 = memapp2
icT38 = memapp3
ict39 = nthmem
icT40 = subsetunion
icT41 = subsetintersect
icT42 = memunion1
icT43 = memunion2
icT44 = memintersect
icT45 = memins
icT46 = meminsert1
icT47 = meminsert2
icT48 = lensort
icT49 = memsort1
icT50 = countsort
*/

benchmark_plan ireland_critics_lemma_spec Meth Query :-
        testloop (% interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list objlists,
        (add_theory_defs_to_sym_eval_list list_benchmarks,
        (add_theory_defs_to_sym_eval_list map_benchmarks,
	(add_theory_defs_to_sym_eval_list clam_corpus,
	(add_theory_defs_to_sym_eval_list ireland_critics_lemma_spec,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query))))))))))
        ).

end



