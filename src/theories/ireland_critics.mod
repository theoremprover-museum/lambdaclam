/* 

File: ireland_critics.mod
Author: Louise Dennis
Description: Examples taken from Productive Use of Failure in
Inductive Proof by Andrew and Alan B.  These are the example problems
on which clam 3 was tested.
Created: 21st May 2002

*/

module ireland_critics.

accumulate clam_corpus.

/*
local icdummy osyn -> o.
icdummy X.
local icdummy2 osyn -> o.
icdummy2 X.
local icdummy3 osyn -> o.
icdummy3 X.
local icdummy4 osyn -> o.
icdummy4 X.
local icdummy5 osyn -> o.
icdummy5 X:- printstdout X.
local icdummy6 osyn -> o.
icdummy6 X.
local icdummy7 osyn -> o.
icdummy7 X:- printstdout X.
*/


/* ict27 = qrevcorrect */

has_otype ireland_critics qrevflat (arrow [(olist (olist X)), (olist X)] (olist X)).
has_otype ireland_critics orevflat (arrow [(olist (olist X))] (olist X)).

definition ireland_critics qrevflat1 
        trueP
        (app qrevflat  [onil, L])
        L.
definition ireland_critics qrevflat2
        trueP
        (app qrevflat  [(app ocons  [H, T]), L])
        (app qrevflat  [T, (app oapp  [H, L])]).

definition ireland_critics orevflat1  trueP 
    (app orevflat [onil]) 
    onil.
definition ireland_critics orevflat2  trueP   
    (app orevflat [(app ocons  [H, T])]) 
    (app oapp  [(app orevflat [T]), H]). 


lemma ireland_critics oapp_lem equiv 
      trueP
      (app oapp [(app oapp [X, (app ocons [Y, onil])]), Z])
      (app oapp [X, (app ocons [Y, Z])]).

top_goal ireland_critics icT28 []
	(app forall  [(olist (olist nat)), (abs (x\
	(app eq  [(app orevflat [x]), (app qrevflat  [x, onil])])) (olist (olist nat)))]).

top_goal ireland_critics icT29 []
	(app forall  [(olist nat), (abs (x\
	(app eq  [(app orev [(app qrev  [x, onil])]), x])) (olist nat))]).

top_goal ireland_critics icT30 []
	(app forall  [(olist nat), (abs (x\
	(app eq  [(app orev [(app oapp  [(app orev [x]), onil])]), x])) (olist nat))]).


top_goal ireland_critics icT31 []
	(app forall  [(olist nat), (abs (x\
	(app eq  [(app qrev  [(app qrev  [x, onil]), onil]), x])) (olist nat))]). 

top_goal ireland_critics icT31b []
	(app forall  [(olist nat), (abs (x\
	(app eq  [(app qrev  [x, onil]), (app oapp [(app orev [x]), onil])])) (olist nat))]). 

top_goal_c ireland_critics icT32 []
	(app forall  [(olist nat), (abs  (l\ 
		(app eq  [(app rotate  [(app olength [l]), l]),
				 l])) (olist nat))]) 
	[].


has_otype ireland_critics fac (arrow [nat] nat).
definition ireland_critics fac1
	trueP
	(app fac [zero])
	(app s [zero]).
definition ireland_critics fac2
	trueP
	(app fac [(app s [N])])
	(app otimes  [(app fac [N]), (app s [N])]).


has_otype ireland_critics qfac (arrow [nat, nat] nat).
definition ireland_critics qfac1
        trueP
        (app qfac  [zero, X])
        X.
definition ireland_critics qfac2
        trueP
        (app qfac  [(app s [N]), X])
        (app qfac  [N, (app otimes  [(app s [N]), X])]).

lemma ireland_critics ass_otimes equiv
	trueP
	(app otimes [(app otimes [X, Y]), Z])
	(app otimes [X, (app otimes [Y, Z])]).

lemma ireland_critics ass_plus equiv
	trueP
	(app plus [(app plus [X, Y]), Z])
	(app plus [X, (app plus [Y, Z])]).

lemma ireland_critics plus1_right equiv
      trueP
      (app plus [X, zero])
      X.

lemma ireland_critics times1_right equiv
      trueP
      (app otimes [X, zero])
      zero.

lemma ireland_critics plus_right equiv
      trueP
      (app plus [X, (app s [Y])])
      (app s [(app plus [X, Y])]).

lemma ireland_critics times_right equiv
      trueP
      (app otimes [X, (app s [Y])])
      (app plus [(app otimes [X, Y]), X]).

has_otype arithmetic qtimes (arrow [nat, nat, nat] nat).
definition arithmetic qtimes1 trueP
   (app qtimes  [zero, _, X]) 
   X.
definition arithmetic qtimes2 trueP
   (app qtimes  [(app s [Y]), X, Z]) 
   (app qtimes  [Y, X, (app plus  [Z, X])]).



has_otype ireland_critics qexp (arrow [nat, nat, nat] nat).
definition ireland_critics qexp1 trueP
   (app qexp  [_, zero, X]) 
   X.
definition ireland_critics qexp2 trueP
   (app qexp  [X, (app s [Y]), Z]) 
   (app qexp  [X, Y, (app otimes  [X, Z])]).


top_goal_c ireland_critics icT33 []
        (app forall  [nat, (abs (x\
                (app eq  [(app qfac  [x, (app s [zero])]), (app fac [x])])) nat)]) [].

top_goal ireland_critics icT34 []
        (app forall  [nat, (abs (x\
                (app forall  [nat, (abs (y\
        (app eq  [(app otimes  [x, y]),
                        (app qtimes  [x, y, zero])])) nat)])) nat)]).

top_goal ireland_critics icT35 []
        (app forall  [nat, (abs (x\
                (app forall  [nat, (abs (y\
        (app eq  [(app exp  [x, y]),
                        (app qexp  [x, y, (app s [zero])])])) nat)])) nat)]).

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

benchmark_plan ireland_critics Meth Query :-
        testloop (% interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2, ass_otimes, ass_oapp, oapp_lem, qrev1, qrev2, rotate1, rotate2, ass_plus],
        (add_theory_defs_to_sym_eval_list arithmetic,
	(delete_from_sym_eval_list [fun_iter1, fun_iter2, fun_iter3],
        (add_theory_defs_to_sym_eval_list objlists,
%        (add_theory_defs_to_sym_eval_list list_benchmarks,
%        (add_theory_defs_to_sym_eval_list map_benchmarks,
%	(add_theory_defs_to_sym_eval_list clam_corpus,
	(add_theory_defs_to_sym_eval_list ireland_critics,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query))))))))
        ).

end



