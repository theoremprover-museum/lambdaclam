/*

File: list_benchmarks.mod
Author: Louise Dennis
Description:  List based theorems for benchmarking.
Last Modified: 20th March 2001

*/

module list_benchmarks.

accumulate objlists.
accumulate constructive_logic.

/*
local list_benchmark_dummy osyn -> o.
list_benchmark_dummy X.
local listbdummy osyn -> o.
listbdummy X.
local listadummy osyn -> o.
listadummy X.
*/

definition list_benchmarks qrev1 
        trueP
        (app qrev  [onil, L])
        L.
definition list_benchmarks qrev2
        trueP
        (app qrev  [(app ocons  [H, T]), L])
        (app qrev  [T, (app ocons  [H, L])]).


% rotate
%
% (rotate zero L) => L.
definition list_benchmarks rotate1 
	trueP 
	(app rotate  [zero, L])
	L.
%
% (rotate (s N) (ocons H T)) => (rotate N (oapp T (ocons H onil))).
definition list_benchmarks rotate2  
	trueP 
	(app rotate  [(app s [N]), (app ocons  [H, T])])
	(app rotate  [N, (app oapp  [T, (app ocons  [H, onil])])]).

% drop
%
% (drop zero L) => L.
definition list_benchmarks drop1  trueP 
	   (app drop  [zero, L])
	   L.

%
% (drop N onil) => onil.
definition list_benchmarks drop2 trueP 
	   (app drop  [N, onil])
	   onil.

%
% (drop (s X) (ocons H T)) => (drop X T).
definition list_benchmarks drop3 trueP 
	   (app drop  [(app s [X]), (app ocons  [_H, T])])
	   (app drop  [X, T]).

definition list_benchmarks omem1 trueP (app omember  [_X,  onil]) falseP.
definition list_benchmarks omem2 (app neq  [X, Y])
    (app omember  [X, (app ocons  [Y, Z])])
    (app omember  [X, Z]).
definition list_benchmarks omem3 trueP
    (app omember  [X, (app ocons  [X, Z])])
    (trueP).

definition list_benchmarks atend1 
	trueP
	(app atend  [X, onil])
	(app ocons  [X, onil]).
definition list_benchmarks atend2
	trueP
	(app atend  [X, (app ocons  [H, T])])
	(app ocons  [H, (app atend  [X, T])]).

has_otype list_benchmarks atend (arrow [X, (olist X)] (olist X)).
has_otype list_benchmarks omember (arrow [X, (olist X)] bool).
has_otype list_benchmarks drop (arrow [nat, (olist X)] (olist X)). 
has_otype list_benchmarks qrev (arrow [(olist X), (olist X)] (olist X)).
has_otype list_benchmarks rotate (arrow [nat, (olist X)](olist X)).

top_goal list_benchmarks qrevcorrect []
	(app forall  [(olist nat), (abs (l\
		(app eq  [(app orev [l]), 
			        (app qrev  [l, onil])])) (olist nat))]).


top_goal list_benchmarks rotlensimple []
	(app forall  [(olist nat), (abs  (l\ 
		(app eq  [(app rotate  [(app olength [l]), l]),
				 l])) (olist nat))]).

top_goal list_benchmarks app1right []
	(app forall  [(olist nat), (abs (v0\ 
		(app eq  [(app oapp  [v0, onil]),
				 v0])) (olist nat))]).

top_goal list_benchmarks apporev []
	(app forall  [(olist nat), (abs (v0\
		(app forall  [(olist nat), (abs  (v1\ 
	(app eq  [(app oapp  [(app orev [v0]), (app orev [v1])]),
			(app orev [(app oapp  [v1, v0])])])) (olist nat))])) (olist nat))]).

top_goal list_benchmarks cnc_app []
	(app forall  [(olist nat), (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app eq  [v1, v2]),
			(app eq  [(app oapp  [v0, v1]),
					(app oapp  [v0, v2])])])) (olist nat))])) (olist nat))])) (olist nat))]).

top_goal list_benchmarks cnc_cons []
	(app forall  [nat, (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app eq  [v1, v2]),
			 (app eq  [(app ocons  [v0, v1]),
					 (app ocons  [v0, v2])])])) (olist nat))])) (olist nat))])) nat)]).


top_goal list_benchmarks cnc_cons2 []
	(app forall  [nat, (abs (v0\ 
		(app forall  [nat, (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app eq  [v0, v1]),
			(app eq  [(app ocons  [v0, v2]),
					(app ocons  [v1, v2])])])) (olist nat))])) nat)])) nat)]).

top_goal list_benchmarks comapp []
	(app forall  [(olist nat), (abs  (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
	(app eq  [(app olength [(app oapp  [v0, v1])]), 
			(app olength [(app oapp  [v1, v0])])])) (olist nat))])) (olist nat))]).

top_goal list_benchmarks lenorev []
	(app forall  [(olist nat), (abs (v0\ 
		(app eq  [(app olength [v0]),
				(app olength [(app orev [v0])])])) (olist nat))]).

top_goal list_benchmarks lensum []
	(app forall  [(olist nat), (abs  (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
	(app eq  [(app olength [(app oapp  [v0, v1])]), 
			(app plus  [(app olength [v0]),
					  (app olength [v1])])])) (olist nat))])) (olist nat))]).

top_goal list_benchmarks leqnth []
	(app forall  [(olist nat), (abs (v0\ 
		(app forall  [nat, (abs (v1\ 
	(app leq  [(app olength [(app drop  [v1, v0])]), 
			(app olength [v0])])) nat)])) (olist nat))]).

top_goal list_benchmarks memapp2 []
	(app forall  [nat, (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app omember  [v0, v2]),
			 (app omember  [v0, (app oapp  [v1, v2])])])) (olist nat))])) (olist nat))])) nat)]).

top_goal list_benchmarks memapp3 []
	(app forall  [nat, (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app or  [(app omember  [v0, v1]),
					 (app omember  [v0, v2])]),
			 (app omember  [v0, (app oapp  [v1, v2])])])) (olist nat))])) (olist nat))])) nat)]).



top_goal list_benchmarks memorev []
	(app forall  [nat, (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
	(app imp  [(app omember  [v0, v1]),
			 (app omember  [v0, (app orev [v1])])])) (olist nat))])) nat)]).


top_goal list_benchmarks nthapp []
	(app forall  [nat, (abs (v0\ 
		(app forall  [nat, (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app eq  [(app drop  [(app plus  [v0, v1]), v2]),
			(app drop  [v1, (app drop  [v0, v2])])])) (olist nat))])) nat)])) nat)]).

top_goal list_benchmarks nthmem []
	(app forall  [nat, (abs (v0\ 
		(app forall  [nat, (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app omember  [v0, (app drop  [v1, v2])]),
			 (app omember  [v0, v2])])) (olist nat))])) nat)])) nat)]).

top_goal list_benchmarks nthnil []
	(app forall  [nat, (abs (v0\ 
		(app eq  [(app drop  [v0, onil]), 
				onil])) nat)]).

top_goal list_benchmarks orevqrev []
        (app forall  [(olist nat), (abs (x\
                (app forall  [(olist nat), (abs (y\
                        (app eq  [
        (app oapp  [(app orev [x]), y]),
        (app qrev  [x, y])])) (olist nat))])) (olist nat))]).

top_goal list_benchmarks qrevqrev []
	(app forall  [(olist nat), (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
	(app eq  [(app qrev  [(app qrev  [v0, v1]), onil]),
			(app oapp  [(app orev [v1]), (app orev [(app orev [v0])])])])) (olist nat))])) (olist nat))]).

top_goal list_benchmarks orevorev []
	(app forall  [(olist nat), (abs (v0\ 
	(app eq  [(app orev [(app orev [v0])]), v0])) (olist nat))]).

top_goal list_benchmarks rotlen []
	(app forall  [(olist nat), (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
	(app eq  [(app rotate  [(app olength [v0]),
					    (app oapp  [v0, v1])]),
			(app oapp  [v1, v0])])) (olist nat))])) (olist nat))]).
top_goal list_benchmarks singleorev []
	(app forall  [nat, (abs (v0\ 
		(app eq  [(app orev [(app ocons  [v0, onil])]),
				(app ocons  [v0, onil])])) nat)]).

top_goal list_benchmarks tailorev []
	(app forall  [(olist nat), (abs (v0\ 
		(app forall  [nat, (abs (v1\ 
	(app eq  [(app orev [(app oapp  [v0, (app ocons  [v1, onil])])]),
		(app ocons  [v1, (app orev [v0])])])) nat)])) (olist nat))]).
top_goal list_benchmarks tailorev2 []
	(app forall  [(olist nat), (abs (v0\ 
		(app forall  [nat, (abs (v1\ 
	(app eq  [(app oapp  [(app orev [v0]), 
                                          (app ocons  [v1, onil])]),
			(app orev [(app ocons  [v1, v0])])])) nat)])) (olist nat))]).

top_goal list_benchmarks lendouble []
	(app forall  [(olist nat), (abs (l\
		(app eq  [(app olength [(app oapp  [l, l])]),
				(app double [(app olength [l])])])) (olist nat))]).


top_goal list_benchmarks appatend []
	(app forall  [(olist nat), (abs (x\
		(app forall  [nat, (abs (y\
			(app forall  [(olist nat), (abs (z\
	(app eq  [(app oapp  [x, (app ocons  [y, z])]),
			(app oapp  [(app atend  [y, x]), z])])) (olist nat))])) nat)])) (olist nat))]).

%
% Challenge theorems from BBN 1163, section 4.

% solved, using allList_or_left right to left as a rewrite rule.
%
top_goal list_benchmarks 
    allList_omember []
       (app forall  [(olist obj),
         (abs (l\ 
        (app allList  [(abs (x\ (app omember  [x, l])) obj), l])) (olist obj))]).

% Not solved. Originally had a type meta-variable. Removed this as it
% caused nontermination of rewriting.
%
top_goal list_benchmarks allList_omember_imp1 []
  (app forall  [(olist obj),
    (abs (l\ (app forall  [(olist obj),
     (abs (m\ (app forall  [(arrow [nat] bool),
       (abs (x\ 
        ((app imp  [
              (app and   [
                 (app omember  [x, l]),
                 (app allList  [(abs (y\ (app omember  [y, m])) obj), l
])]), 
              (app omember  [x, m])]))) (arrow [nat] bool))])) (olist obj))])) (olist obj))]).

% Not solved. Originally had a type meta-variable. Removed this as 
% for allList_omember_imp1.
%
top_goal list_benchmarks allList_omember_imp2 []
(app forall  [(olist obj), (abs (m\ (app forall  [(olist obj), 
      (abs (l\ (app forall  [(arrow [nat] bool), (abs (x\ 
      ((app imp  [
          (app and  [
                (app omember  [x, l]),
                (app allList  [(abs (x\ (app omember  [x, m])) obj), l])]),
          (app omember  [x, m])]))) (arrow [nat] bool))])) (olist obj))])) (olist obj))]).

% implicit synthesis by instantiation of existentially quantified
% variable (to l in this case).
% 
top_goal list_benchmarks simple_sy []
        (app forall  [(olist nat), (abs (l\ (app exists  [(olist nat)
, (abs (m\ (app forall  [nat, (abs (x\ (app imp  [(app omember  
[x, l]), (app omember  [x, m])])) nat)])) (olist nat))])) (olist nat))]).


top_goal list_benchmarks memapp []
        (app forall  [nat, (abs (a\
                (app forall  [(olist nat), (abs (t\
                        (app forall  [(olist nat), (abs (l\
        (app imp  [(app omember  [a, t]), 
                         (app omember  [a, (app oapp  [t, l])])])) (olist nat))])) (olist nat))])) nat)]).

benchmark_plan list_benchmarks Meth Query :-
	testloop (%interaction_mode command,
	(set_theory_induction_scheme_list arithmetic,
	(add_theory_to_induction_scheme_list objlists,
	(set_sym_eval_list [ass_oapp, beta_idty, idty, s_functional, cons_functional, mono_fun_1, mono_fun_2],
	(add_theory_defs_to_sym_eval_list arithmetic,
	(add_theory_defs_to_sym_eval_list objlists,
	(add_theory_defs_to_sym_eval_list list_benchmarks,
	(set_wave_rule_to_sym_eval,
	pds_plan Meth Query)))))))
	).

/*
File: map_benchmarks.mod
Author: Louise Dennis
Description:  Benchmarks using various higher order functions
Last Modified: 20th March 2001
*/


has_otype map_benchmarks mapcar (arrow [(arrow [A] B), (olist A)] (olist B)).

definition map_benchmarks mapcar1
	trueP
	(app mapcar  [F, onil])
	onil.
definition map_benchmarks mapcar2
	trueP
	(app mapcar  [F, (app ocons  [H, T])])
	(app ocons  [(app F [H]), (app mapcar  [F, T])]).

definition map_benchmarks fil1
	trueP
	(app fil  [F, onil])
	onil.
definition map_benchmarks fil2
	(app F [H])
	(app fil  [F, (app ocons  [H, T])])
	(app ocons  [H, (app fil  [F, T])]).
definition map_benchmarks fil3
	(app neg [(app F [H])])
	(app fil  [F, (app ocons  [H, T])])
	(app fil  [F, T]).

has_otype map_benchmarks fil (arrow [(arrow [X] bool), (olist X)] (olist X)).

has_otype map_benchmarks foldr (arrow [(arrow [X, Y] Y), (olist X), Y] Y).

definition map_benchmarks foldr1
	trueP
	(app foldr  [F, onil, E])
	E.
definition map_benchmarks foldr2
	trueP
	(app foldr  [F, (app ocons  [H, T]), E])
	(app F  [H, (app foldr  [F, T, E])]).

top_goal map_benchmarks filapp []
	(app forall  [(olist nat), (abs (a\
		(app forall  [(olist nat), (abs (b\
			(app forall  [arrow [nat] bool, (abs (f\
	(app eq  [
		(app fil  [f, (app oapp  [a, b])]),
		(app oapp  [
			(app fil  [f, a]),
			(app fil  [f, b])
				])])) (arrow [nat] bool))])) (olist nat))])) (olist nat))]).

top_goal map_benchmarks mapcarapp []
	(app forall  [(arrow [nat] nat), (abs (f\
		(app forall  [(olist nat), (abs (l1\
			(app forall  [(olist nat), (abs (l2\
	(app eq  [(app mapcar  [f, (app oapp  [l1, l2])]),
			(app oapp  [(app mapcar  [f, l1]),
					  (app mapcar  [f, l2])])])) (olist nat))])) (olist nat))])) (arrow [nat] nat))]).

top_goal map_benchmarks mapdouble []
	(app forall  [(olist nat), (abs (l\
		(app eq  [(app mapcar  [double, l]),
				(app mapcar  [(abs (x\ (app plus  [x, x])) nat), l])])) (olist nat))]).


top_goal map_benchmarks mapfoldr []
	(app forall  [(arrow [nat] nat), (abs (f\
		(app forall  [(olist nat), (abs (l\
	(app eq  [(app mapcar  [f, l]),
			(app foldr  [(abs (x\ (abs (t\ (app ocons  [(app f [x]), t])) (olist nat))) nat), l, onil])])) (olist nat))])) (arrow [nat] nat))]).

top_goal map_benchmarks mapthm []
	(app forall  [(arrow [nat] nat), (abs (f\
		(app forall  [(arrow [nat] nat), (abs (g\
			(app forall  [(olist nat), (abs (l\
	(app eq  [(app mapcar  [f, (app mapcar  [g, l])]),
			(app mapcar  [(app fun_compose  [f, g]),
					    l])])) (olist nat))])) (arrow [nat] nat))])) (arrow [nat] nat))]).

top_goal map_benchmarks lenmap []
	(app forall  [(arrow [nat] nat), (abs (f\
		(app forall  [(olist nat), (abs (l\
	(app eq  [(app olength [(app mapcar  [f, l])]),
			(app olength [l])])) (olist nat))])) (arrow [nat] nat))]).

top_goal map_benchmarks mapapn []
	(app forall  [(arrow [nat] nat), (abs (f\
		(app forall  [nat, (abs (n\
			(app forall  [(olist nat), (abs (t\
				(app forall  [nat, (abs (h\
	(app eq  [
		(app (app fun_iter  [n, (app mapcar [f])]) [(app ocons  [h, t])]),
		(app ocons  [(app (app fun_iter  [n, f]) [h]),
				   (app (app fun_iter  [n, (app mapcar [f])]) [t])])])) nat)])) (olist nat))])) nat)])) (arrow [nat] nat))]).


benchmark_plan map_benchmarks Meth Query :-
	testloop (%interaction_mode command,
	(set_theory_induction_scheme_list arithmetic,
	(add_theory_to_induction_scheme_list objlists,
	(set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2, fun_compose1, and3],
	(add_theory_defs_to_sym_eval_list arithmetic,
	(add_theory_defs_to_sym_eval_list objlists,
	(add_theory_defs_to_sym_eval_list list_benchmarks,
	(add_theory_defs_to_sym_eval_list map_benchmarks,
	(set_wave_rule_to_sym_eval,
	(add_to_sym_eval_list [beta_reduction],
	pds_plan Meth Query)))))))))
	).


end

