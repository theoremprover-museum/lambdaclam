/*

File: clam_corpus.mod
Author: Louise Dennis
Description:  Clam theorems for benchmarking.
Last Modified: 28th May 2001

*/

module clam_corpus.

accumulate list_benchmarks.

%% Predicate to get thing to compile
local cc_pred osyn -> o.
cc_pred X.
local cc1 osyn -> o.
cc1 X.

has_otype clam_corpus sort (arrow [(olist nat)] (olist nat)).
definition clam_corpus sort1
	trueP
	(app sort [onil])
	onil.
definition clam_corpus sort2
	trueP
	(app sort [(app ocons [H, T])])
	(app insert [H, (app sort [T])]).

has_otype clam_corpus insert (arrow [nat, (olist nat)](olist nat)).
definition clam_corpus insert1
	trueP
	(app insert  [N, onil])
	(app ocons  [N, onil]).
definition clam_corpus insert2
	(app less  [N, H])
	(app insert  [N, (app ocons  [H, T])])
	(app ocons  [N, (app ocons  [H, T])]).
definition clam_corpus insert3
	(app neg [(app less  [N, H])])
	(app insert  [N, (app ocons  [H, T])])
	(app ocons  [H, (app insert  [N, T])]).

has_otype clam_corpus count (arrow [X, (olist X)] nat).
definition clam_corpus count1
	trueP
	(app count  [A, onil])
	zero.
definition clam_corpus count2
	(app eq  [A, H])
	(app count  [A, (app ocons  [H, T])])
	(app s [(app count  [A, T])]).
definition clam_corpus count3
	(app neq  [A, H])
	(app count  [A, (app ocons  [H, T])])
	(app count  [A, T]).

has_otype clam_corpus odd (arrow [nat] bool).
definition clam_corpus odd1 trueP
(app odd [zero])
falseP.
definition clam_corpus odd2 trueP
(app odd [(app s [zero])])
trueP.
definition clam_corpus odd3 trueP
(app odd [(app s [(app s [X])])])
(app odd [X]).


has_otype clam_corpus geq (arrow [nat, nat] bool).
axiom clam_corpus geq1 equiv
	trueP
	(app geq  [X, zero])
	trueP.
axiom clam_corpus geq2 equiv
	trueP
	(app geq  [zero, (app s [X])])
	falseP.
axiom clam_corpus geq3 equiv
	trueP
	(app geq  [(app s [X]), (app s [Y])])
	(app geq  [X, Y]).
lemma clam_corpus geq_transitive equiv 
        trueP
        (app transitive [geq])
        trueP.

has_otype clam_corpus greater (arrow [nat, nat] bool).
axiom clam_corpus greater1 equiv
	trueP
	(app greater  [zero, X])
	falseP.
axiom clam_corpus greater1 equiv
	trueP
	(app greater  [(app s [X]), zero])
	trueP.
axiom clam_corpus greater3 equiv
	trueP
	(app greater  [(app s [X]), (app s [Y])])
	(app greater  [X, Y]).
lemma clam_corpus greater_transitive equiv 
        trueP
        (app transitive [greater])
        trueP.

has_otype clam_corpus intersect (arrow [(olist X), (olist X)] (olist X)).
definition clam_corpus intersect1
	trueP
	(app intersect  [onil, L2])
	onil.
definition clam_corpus intersect2
	trueP
	(app intersect  [L1, onil])
	onil.
definition clam_corpus intersect3
	(app omember  [H, L2])
	(app intersect  [(app ocons  [H, T]), L2])
	(app ocons  [H, (app intersect  [T, L2])]).
definition clam_corpus intersect4
	(app neg [(app omember  [H, L2])])
	(app intersect  [(app ocons  [H, T]), L2])
	(app intersect  [T, L2]).

has_otype clam_corpus union (arrow [(olist X), (olist X)] (olist X)).
definition clam_corpus union1
	trueP
	(app union  [onil, L2])
	L2.
definition clam_corpus union2
	trueP
	(app union  [L1, onil])
	L1.
definition clam_corpus union3
	(app omember  [H, L2])
	(app union  [(app ocons  [H, L1]), L2])
	(app union  [L1, L2]).
definition clam_corpus union4
	(app neg [(app omember  [H, L2])])
	(app union  [(app ocons  [H, T]), L2])
	(app ocons  [H, (app union  [T, L2])]).

has_otype clam_corpus min (arrow [nat, nat] nat).
definition clam_corpus min1
	trueP
	(app min [zero, X])
	zero.
definition clam_corpus min2
	trueP
	(app min [X, zero])
	zero.
definition clam_corpus min3
	trueP
	(app min [(app s [X]), (app s [Y])])
	(app s [(app min [X, Y])]).

has_otype clam_corpus max (arrow [nat, nat] nat).
definition clam_corpus max1
	trueP
	(app max [zero, X])
	X.
definition clam_corpus max2
	trueP
	(app max [X, zero])
	X.
definition clam_corpus max3
	trueP
	(app max [(app s [X]), (app s [Y])])
	(app s [(app max [X, Y])]).


has_otype clam_corpus ordered (arrow [(olist nat)] bool).
definition clam_corpus ordered1
	trueP
	(app ordered [onil])
	trueP.
definition clam_corpus ordered2
	trueP
	(app ordered [(app ocons  [X, onil])])
	trueP.
definition clam_corpus ordered3
	(app less  [Y, X])
	(app ordered [(app ocons  [X, (app ocons  [Y, T])])])
	falseP.
definition clam_corpus ordered4
	(app neg [(app less  [Y, X])])
	(app ordered [(app ocons  [X, (app ocons  [Y, T])])])
	(app ordered [(app ocons [Y, T])]).

has_otype clam_corpus subset (arrow [(olist X), (olist X)] bool).
definition clam_corpus subset1
	trueP
	(app subset  [onil, L])
	trueP.
definition clam_corpus subset2
	(app neg [(app omember  [H, Y])])
	(app subset  [(app ocons  [H, X]), Y])
	falseP.
definition clam_corpus subset3
	(app omember  [H, Y])
	(app subset  [(app ocons  [H, X]), Y])
	(app subset  [X, Y]).


top_goal clam_corpus countsort []
	(app forall  [nat, (abs (a\
		(app forall  [(olist nat), (abs (l\
	(app eq  [(app count  [a, (app sort [l])]),
			(app count  [a, l])])) (olist nat))])) nat)]).

top_goal clam_corpus evenodd1 []
	(app forall  [nat, (abs (x\
		(app imp  [(app even [x]),
				 (app neg [(app odd [x])])])) nat)]).

top_goal clam_corpus evenodd2 []
	(app forall  [nat, (abs (x\
		(app imp  [(app odd [x]),
				 (app neg [(app even [x])])])) nat)]).

top_goal clam_corpus geqdouble []
	(app forall  [nat, (abs (x\
		(app geq  [(app double [x]), x])) nat)]).

top_goal clam_corpus geqdoublehalf []
	(app forall  [nat, (abs (x\
		(app geq  [(app double [x]), (app half [x])])) nat)]).

top_goal clam_corpus geqhalf []
	(app forall  [nat, (abs (x\
		(app geq  [x, (app half [x])])) nat)]).

top_goal clam_corpus geqnotlessp []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app geq  [x, y]),
			 (app neg [(app less  [x, y])])])) nat)])) nat)]).

% clam 2 couldn't do this.
top_goal clam_corpus greatercancel []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app imp  [(app greater  [z, zero]),
		(app imp  [(app greater  [x, y]),
			(app greater  [(app otimes  [z, x]),
					     (app otimes  [z, y])])])])) nat)])) nat)])) nat)]).

top_goal clam_corpus greatercons []
	(app forall  [nat, (abs (h\
		(app forall  [(olist nat), (abs (t\
	(app greater  [(app olength [(app ocons  [h, t])]),
			     (app olength [t])])) (olist nat))])) nat)]).

top_goal clam_corpus greaterplus []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app imp  [(app greater  [x, y]),
			 (app greater  [(app plus  [z, x]), y])])) nat)])) nat)])) nat)]).

top_goal clam_corpus greaterplus2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app imp  [(app greater  [x, y]),
			 (app greater  [(app plus  [x, z]), y])])) nat)])) nat)])) nat)]).

% clam 2 couldn't do this
top_goal clam_corpus greaterplus3 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
				(app forall  [nat, (abs (w\
	(app imp  [(app greater  [x, y]),
		(app imp  [(app greater  [z, w]),
			(app greater  [(app plus  [x, z]),
					     (app plus  [y, w])])])])) nat)])) nat)])) nat)])) nat)]).

top_goal clam_corpus greaters []
	(app forall  [nat, (abs (x\
		(app greater  [(app s [x]), x])) nat)]).

top_goal clam_corpus greaters2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app imp  [(app greater  [x, y]),
					 (app greater  [(app s [x]), y])])) nat)])) nat)]).

top_goal clam_corpus greaterss []
	(app forall  [nat, (abs (x\
		(app greater  [(app s [(app s [x])]), x])) nat)]).

% Apparently requires greaterplus
top_goal clam_corpus greatertimes []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app imp  [(app greater  [z, zero]),
		(app imp  [(app greater  [x, y]),
			(app greater  [(app otimes  [z, x]), y])])])) nat)])) nat)])) nat)]).

% clam 2 couldn't do this.
top_goal clam_corpus grsqsuc []
	(app forall  [nat, (abs (n\
		(app imp  [(app greater  [n, (app s [zero])]),
		 (app greater  [(app otimes  [n, n]), (app s [n])])])) nat)]).

top_goal clam_corpus lensort []
	(app forall  [(olist nat), (abs (l\
		(app eq  [(app olength [(app sort [l])]), (app olength [l])])) (olist nat))]).

top_goal clam_corpus less_double_mono []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app less  [x, y]),
			 (app less  [(app double [x]), (app double [y])])])) nat)])) nat)]).

top_goal clam_corpus less_double_mono2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app less  [(app double [x]), (app double [y])]),
			 (app less  [x, y])
                        ])) nat)])) nat)]).

top_goal clam_corpus lesseq []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app and  [(app neq  [x, y]),
					  (app leq  [x, y])]),
			 (app less  [x, y])])) nat)])) nat)]).

top_goal clam_corpus lessleq1 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app neg [(app leq  [x, y])]),
			 (app less  [y, x])])) nat)])) nat)]).

top_goal clam_corpus lessleq2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app neg [(app less  [x, y])]),
			 (app leq  [y, x])])) nat)])) nat)]).

top_goal clam_corpus lesss []
	(app forall  [nat, (abs (x\
		(app less  [x, (app s [x])])) nat)]).

top_goal_c clam_corpus memins []
	(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app omember  [x, (app insert  [x, y])])) (olist nat))])) nat)])
	[(banned [memins1, memins2])].

lemma clam_corpus memins1 rtol trueP
      (app omember [X, (app insert [X, Y])])
      trueP.
lemma clam_corpus memins2 rtol (app neq [A, B])
      (app omember [A, (app insert [B, L])])
      (app omember [A, L]).

%% Next two "need normalise"
top_goal_c clam_corpus meminsert1 []
	(app forall  [nat, (abs (a\
		(app forall  [nat, (abs (b\
			(app forall  [(olist nat), (abs (l\
	(app imp  [(app eq  [a, b]),
		(app omember  [a, (app insert  [b, l])])])) (olist nat))])) nat)])) nat)])
	[(banned [memins1, memins2])].

top_goal_c clam_corpus meminsert2 []
	(app forall  [nat, (abs (a\
		(app forall  [nat, (abs (b\
			(app forall  [(olist nat), (abs (l\
	(app imp  [(app neq  [a, b]),
		(app eq  [
			(app omember  [a, (app insert  [b, l])]),
			(app omember  [a, l])])])) (olist nat))])) nat)])) nat)])
	[(banned [memins1, memins2])].

top_goal clam_corpus memintersect []
	(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (a\
			(app forall  [(olist nat), (abs (b\
	(app imp  [(app and  [(app omember  [x, a]),
					  (app omember  [x, b])]),
			 (app omember  [x, (app intersect  [a, b])])])) (olist nat))])) (olist nat))])) nat)]).

top_goal clam_corpus memsort1 []
	(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (l\
			(app imp  [(app omember  [x, (app sort [l])]),
					 (app omember  [x, l])])) (olist nat))])) nat)]).

top_goal clam_corpus memsort2 []
	(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (l\
			(app imp  [(app omember  [x, l]),
					(app omember  [x, (app sort [l])])])) (olist nat))])) nat)]).

top_goal clam_corpus memunion1 []
	(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (a\
			(app forall  [(olist nat), (abs (b\
	(app imp  [(app omember  [x, a]),
			 (app omember  [x, (app union  [a, b])])])) (olist nat))])) (olist nat))])) nat)]).

top_goal clam_corpus memunion2 []
	(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (a\
			(app forall  [(olist nat), (abs (b\
	(app imp  [(app omember  [x, b]),
			 (app omember  [x, (app union  [a, b])])])) (olist nat))])) (olist nat))])) nat)]).

top_goal clam_corpus minmax []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app leq  [(app min  [x, y]),
			 (app max  [x, y])])) nat)])) nat)]).

top_goal clam_corpus minmaxgeq []
	(app forall  [nat, (abs (a\
	(app forall  [nat, (abs (b\
	(app forall  [nat, (abs (c\
	(app forall  [nat, (abs (d\
	(app imp  [(app and  [(app geq  [a, c]),
					  (app geq  [b, d])]),
			 (app geq  [(app max  [a, b]), 							  (app min  [c, d])])])) nat)])) nat)])) nat)])) nat)]).


top_goal clam_corpus notlesstrans []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app imp  [(app leq  [z, y]),
		(app imp  [(app less  [x, z]),
				 (app less  [x, y])])])) nat)])) nat)])) nat)]).	
top_goal clam_corpus notlesstrans2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app imp  [
		(app and  [(app less  [x, z]),
				 (app leq  [y, x])]),
				 (app less  [y, z])])) nat)])) nat)])) nat)]).

top_goal clam_corpus ordered_cons []
	(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app imp  [
		(app ordered [(app ocons  [x, y])]),
		(app ordered [y])])) (olist nat))])) nat)]).

top_goal clam_corpus plusgeq []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app geq  [(app plus  [x, y]),
				x])) nat)])) nat)]).

top_goal clam_corpus plusgeq2 []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app geq  [(app plus  [x, y]),
				y])) nat)])) nat)]).

top_goal clam_corpus plusless []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [nat, (abs (z\
	(app imp  [
		(app less  [x, y]),
		(app less  [x, (app plus  [y, z])])])) nat)])) nat)])) nat)]).


top_goal clam_corpus subsetcons []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
			(app forall  [nat, (abs (n\
	(app imp  [(app subset  [x, y]),
			 (app subset  [x, (app ocons  [n, y])])])) nat)])) (olist nat))])) (olist nat))]).

top_goal clam_corpus subsetintersect []
	(app forall  [(olist nat), (abs (a\
		(app forall  [(olist nat), (abs (b\
	(app imp  [(app subset  [a, b]),
			 (app eq  [(app intersect  [a, b]), a])])) (olist nat))])) (olist nat))]).

top_goal clam_corpus times_less []
	(app forall  [nat, (abs (x\
		(app forall  [nat, (abs (y\
	(app imp  [(app and  [(app less  [zero, x]),
				  	  (app less  [zero, y])]),
			 (app less  [zero, (app otimes  [x, y])])])) nat)])) nat)]).

top_goal clam_corpus subsetunion []
	(app forall  [(olist nat), (abs (a\
		(app forall  [(olist nat), (abs (b\
	(app imp  [(app subset  [a, b]),
			 (app eq  [(app union  [a, b]), b])])) (olist nat))])) (olist nat))]).


benchmark_plan clam_corpus Meth Query :-
        testloop (%interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2, leq1, leq2, leq_ss, less1, less2, less3, geq1, geq2, geq3, greater1, greater2, greater3, neq_zero_s, neq_s_zero, and1, and2, and3, and4, neq_eq, imp1, imp2, imp3, memins1, memins2],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list objlists,
        (add_theory_defs_to_sym_eval_list list_benchmarks,
        (add_theory_defs_to_sym_eval_list map_benchmarks,
        (add_theory_defs_to_sym_eval_list clam_corpus,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query))))))))
        )).

%% Compilation aid

end
