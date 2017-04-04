/* 

File: yoshidaetal.mod
Author: Louise Dennis
Description: Examples taken from Coloured rippling:  An extension of a theorem proving heuristic.  Tetsuya Yoshisa, Alan Bundy, Ian Green, Toby Walsh, David Basin, ECAI 94.  Omitting LIM examples (see lim_plus.mod) and those involving duptree and labelcount whose definitions were unclear to me.
Created: 14th September 2005

*/

module yoshidaetal.

accumulate clam_corpus.

local yea osyn -> o.
yea X.

is_otype yoshidaetal (otree X) [oleaf] [onode].

has_otype yoshidaetal oleaf (arrow [X] (otree X)).
has_otype yoshidaetal onode (arrow [X, (otree X), (otree X)] (otree X)).

induction_scheme yoshidaetal tree_struct
	(otree T)
	(dom (a\ (dom b\ (dom c\ (repl c (app onode  [a, b, c]))))))
	(measured (otree T) Prop)
	% Goal
	(seqGoal (H >>> (app forall  [(otree T), (abs Prop (otree T))])) Context)
	% Step Case
	(
 	 (allGoal (otree T)
	 l\ (allGoal (otree T)
	 r\ (allGoal T
	 n\ (seqGoal (((hyp (otype_of n T) nha)::
		       (hyp (otype_of l (otree T)) nha)::
		       (hyp (otype_of r (otree T)) nha)::
                       (hyp (Prop l) ind_hyp)::
	               (hyp (Prop r) ind_hyp)::H)
              >>> (Prop (app onode  [n, l, r]))) Context))))
          **
         % Base Case
	   (allGoal T l\ (seqGoal (((hyp (otype_of l T) nha)::H) >>> Prop (app oleaf [l])) Context))
	).



has_otype yoshidaetal maxht (arrow [(otree X)] nat).
definition yoshidaetal maxht1 trueP
	(app maxht [(app oleaf [X])])
	(app s [zero]).
definition yoshidaetal maxht2 trueP
	(app maxht [(app onode  [X, L, R])])
	(app s [(app max  [(app maxht [L]), (app maxht [R])])]).

has_otype yoshidaetal minht (arrow [(otree X)] nat).
definition yoshidaetal maxht1 trueP
	(app minht [(app oleaf [X])])
	(app s [zero]).
definition yoshidaetal minht2 trueP
	(app minht [(app onode  [X, L, R])])
	(app s [(app min  [(app minht [L]), (app minht [R])])]).

has_otype yoshidaetal tipcount (arrow [(otree X)] nat).
definition yoshidaetal tipcount1 trueP
	(app tipcount [(app oleaf [X])])
	(app s [zero]).
definition yoshidaetal tipcount2 trueP
	(app tipcount [(app onode  [X, L, R])])
	(app plus  [(app tipcount [L]), (app tipcount [R])]).

has_otype yoshidaetal duptree (arrow [(otree nat)] (otree nat)).
definition yoshidaetal duptree1 trueP
	(app duptree [(app oleaf [X])])
	(app onode [zero, (app oleaf [X]), (app oleaf [X])]).
definition yoshidaetal duptree2 trueP
	(app duptree [(app onode [X, L, R])])
	(app onode [X, (app duptree [L]), (app duptree [R])]).

has_otype yoshidaetal nodecount (arrow [(otree X)] nat).
definition yoshidaetal nodecount1 trueP
	(app nodecount [(app oleaf [X])])
	(zero).
definition yoshidaetal nodecount2 trueP
	(app nodecount [(app onode  [X, L, R])])
	(app s [(app plus  [(app nodecount [L]), (app nodecount [R])])]).

has_otype yoshidaetal flattentree (arrow [(otree X)] (olist X)).
definition yoshidaetal flattentree1 trueP
	(app flattentree [(app oleaf [X])])
	(app ocons  [X, onil]).
definition yoshidaetal flattentree2 trueP
	(app flattentree [(app onode  [X, L, R])])
	(app oapp  [(app flattentree [L]), (app ocons  [X, (app flattentree [R])])]).

has_otype yoshidaetal swap (arrow [(otree X)] (otree X)).
definition yoshidaetal swap1 trueP
	(app swap [(app oleaf [X])])
	(app oleaf [X]).
definition yoshidaetal swap2 trueP
	(app swap [(app onode  [X, L, R])])
	(app onode  [X, (app swap [R]), (app swap [L])]).


has_otype yoshidaetal maptree (arrow [(arrow [X] Y), (otree X)] (otree Y)).
definition yoshidaetal maptree1 trueP
	(app maptree  [F, (app oleaf [X])])
	(app oleaf [(app F [X])]).
definition yoshidaetal maptree2 trueP
	(app maptree  [F, (app onode  [X, L, R])])
	(app onode  [(app F [X]), (app maptree  [F, L]), (app maptree  [F, R])]).

lemma yoshidaetal assplus equiv trueP
	(app plus [X, (app plus [Y, Z])])
	(app plus [(app plus [X, Y]), Z]).

lemma yoshidaetal complus equiv trueP
	(app plus [X, Y])
	(app plus [Y, X]).

lemma yoshidaetal maxmin1 rtol trueP
	(app geq  [(app max  [U1, U2]), (app min  [V1, V2])])
	(app and  [(app geq  [U1, V1]), (app geq  [U2, V2])]).

lemma yoshidaetal greatermax rtol trueP
	(app greater  [(app max  [U1, U2]), (app max  [V1, V2])])
	(app and  [(app greater  [U1, V1]), (app greater  [U2, V2])]).

lemma yoshidaetal maxmin2 rtol trueP
	(app geq  [(app max  [U1, U2]), (app min  [V1, V2])])
	(app and  [(app geq  [U1, V2]), (app geq  [U2, V1])]).

lemma yoshidaetal lenoapp equiv trueP
	(app olength [(app oapp  [A, B])])
	(app plus  [(app olength [A]), (app olength [B])]).

lemma yoshidaetal plusand rtol trueP
	(app eq  [(app plus  [X, Y]), (app plus  [A, B])])
	(app and  [(app eq  [X, A]), (app eq  [Y, B])]).

lemma yoshidaetal greaterand rtol trueP
	(app greater  [(app plus  [X, Y]), (app plus  [A, B])])
	(app and  [(app greater  [X, A]), (app greater  [Y, B])]).

top_goal yoshidaetal maxhtgeqminht []
	(app forall  [(otree nat), (abs (t\
	(app geq  [(app maxht [t]), (app minht [t])])) (otree nat))]).

top_goal yoshidaetal tipcountswap []
	(app forall  [(otree nat), (abs (t\
	(app eq  [(app tipcount [(app swap [t])]), (app tipcount [t])])) (otree nat))]).

top_goal yoshidaetal tipcountduptree []
	(app forall  [(otree nat), (abs (t\
	(app greater  [(app tipcount [(app duptree [t])]), (app tipcount [t])])) (otree nat))]).

top_goal yoshidaetal maxhtduptree []
	(app forall  [(otree nat), (abs (t\
	(app greater  [(app maxht [(app duptree [t])]), (app maxht [t])])) (otree nat))]).

top_goal yoshidaetal tipcountnodecount []
	(app forall  [(otree nat), (abs (t\
	(app eq  [(app tipcount [t]), 
                  (app s [(app nodecount [t])])])) (otree nat))]).

top_goal yoshidaetal swapswap []	
	(app forall  [(otree nat), (abs (t\
	(app eq  [(app swap [(app swap [t])]), t])) (otree nat))]).

top_goal yoshidaetal flattenswap []	
	(app forall  [(otree nat), (abs (t\
	(app eq  [(app flattentree [(app swap [t])]), (app orev [(app flattentree [t])])])) (otree nat))]).


top_goal yoshidaetal flattenmap []	
	(app forall  [(otree nat), (abs (t\
		(app forall  [(arrow [nat] nat), (abs (f\
	(app eq  [(app flattentree [(app maptree [f, t])]), (app mapcar [f, (app flattentree [t])])])) (arrow [nat] nat))])) (otree nat))]).

top_goal yoshidaetal lengthflattentree []
	(app forall  [(otree nat), (abs (t\
	(app eq  [(app olength [(app flattentree [t])]), (app tipcount [t])])) (otree nat))]).	

top_goal yoshidaetal swapmaptree []
	(app forall  [(otree nat), (abs (t\
		(app forall  [(arrow [nat] nat), (abs (f\
	(app eq  [(app swap [(app maptree  [f, t])]),
                        (app maptree  [f, (app swap [t])])])) (arrow [nat] nat))])) (otree nat))]).


benchmark_plan yoshidaetal Meth Query :-
        testloop (%interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list objlists,
        (add_theory_to_induction_scheme_list yoshidaetal,
        (set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2, geq1, geq2, geq3, greater1, greater2, greater3, lenoapp, greaterand, plusand, maxmin1, maxmin2, mapcar1, mapcar2, greatermax, greater_transitive],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list objlists,
        (add_theory_defs_to_sym_eval_list list_benchmarks,
        (add_theory_defs_to_sym_eval_list clam_corpus,
        (add_theory_defs_to_sym_eval_list yoshidaetal,
        (set_wave_rule_to_sym_eval,
%	(add_to_wave_rule_list [assplus, complus],
        pds_plan Meth Query)))))))))
% )
        )).

end

