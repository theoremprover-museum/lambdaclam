/*

File: arithmetic.mod
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2000

*/

module pdd_test_times1_plus.

accumulate pdd_repair.
accumulate constructive_logic.

/*
local ptadummy osyn -> o.
ptadummy X.
local ptadummy2 osyn -> o.
ptadummy2 X.
local ptadummy3 osyn -> o.
ptadummy3 X.
*/

%% Results
%% comm - times1 - incorrect synthesis heap overflow
%% dist - times1 - heap overlow
%% distr - times1 - evalute hangs
%% assm - times1 - evaluate hangs
%% zerotimes - empty incorrect rewrite rule.
%% times2right - times1 - evaluate hangs
%% expplus - times1 - evaluate hangs
%% exptimes -



/* SYNTAX CONSTANTS */

is_otype pdd_test_times1_plus nat [zero] [s].

has_otype pdd_test_times1_plus zero nat.
has_otype pdd_test_times1_plus s (arrow [nat] nat).
has_otype pdd_test_times1_plus plus (arrow [nat, nat] nat).
has_otype pdd_test_times1_plus minus (arrow [nat, nat] nat).
has_otype pdd_test_times1_plus otimes (arrow [nat, nat] nat).
has_otype pdd_test_times1_plus exp (arrow [nat, nat] nat).
has_otype pdd_test_times1_plus pdd_leq (arrow [nat, nat] bool).
has_otype pdd_test_times1_plus half (arrow [nat] nat).
has_otype pdd_test_times1_plus double (arrow [nat] nat).
has_otype pdd_test_times1_plus even (arrow [nat] bool).

injective_right plus.
injective_left plus.

injective_right otimes.
injective_left otimes.

injective_right exp.
injective_left exp.

lemma arithmetic mono_fun_1 equiv trueP 
(app eq [(app F [X, Y]), (app F [X, Z])]) 
(app eq [Y, Z]):-
     injective_right F.

lemma arithmetic mono_fun_2 equiv trueP 
(app eq [(app F [Y, X]), (app F [Z, X])]) 
(app eq [Y, Z]):-
     injective_left F.




has_otype pdd_test_times1_plus pred (arrow [nat] nat).
definition pdd_test_times1_plus pred1
	trueP
	(app pred [zero])
	zero.
definition pdd_test_times1_plus pred2
	trueP
	(app pred [(app s [X])])
	X.

known_false (app eq [zero, (app s [X])]).
known_false (app eq [(app s [X]), zero]).

% Basic rewrites
%

lemma pdd_test_times1_plus neq_zero_s equiv trueP (app eq [zero, (app s _)]) 
                                        falseP.
lemma pdd_test_times1_plus neq_s_zero equiv trueP (app eq [(app s _), zero]) 
                                        falseP.
lemma pdd_test_times1_plus neq_eq equiv trueP (app neq [X, X]) falseP.


% plus
%
definition pdd_test_times1_plus plus1 trueP (app plus [zero, Y]) Y.
definition pdd_test_times1_plus plus2 trueP
     (app plus [(app s [Y]), X]) 
     (app s [(app plus [Y, X])]).

top_goal_c pdd_test_times1_plus simple [] (app eq [zero, (app plus [zero, (app plus [zero,  zero])])]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_times1_plus 
%
top_goal_c pdd_test_times1_plus assp []
    (app forall [nat, 
     (abs (z\ (app forall [nat, 
      (abs (y\ (app forall [nat, 
       (abs (x\ (app eq [
        (app plus [(app plus [x, y]), z]), 
        (app plus [x, (app plus [y, z])])])) nat)])) nat)])) nat)]) [(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_times1_plus 
%
top_goal_c pdd_test_times1_plus comp []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app plus [y, x]), (app plus [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_times1_plus plus2right []
	(app forall [nat,
         (abs (y\ (app forall [nat,
	  (abs (x\ (app eq [
           (app plus [x, (app s [y])]),
           (app s [(app plus [x, y])])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_times1_plus plus1lem []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [x, (app s [zero])]),
			(app s [x])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_times1_plus plusxx []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [(app s [x]), x]),
			(app s [(app plus [x, x])])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_times1_plus zeroplus []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app imp [(app and [
				(app eq [x, zero]),
				(app eq [y, zero])]),
			(app eq [(app plus [x, y]), zero])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].


% times
%
definition pdd_test_times1_plus times1 trueP
   (app otimes [zero, X]) 
   (app plus [X, X]).
definition pdd_test_times1_plus times2 trueP
   (app otimes [(app s [Y]), X]) 
   (app plus [(app otimes [Y, X]), X]).

% simple pdd_test_times1_plus 
%
top_goal_c pdd_test_times1_plus comm []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app otimes [y, x]), (app otimes [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_times1_plus 
%

% simple pdd_test_times1_plus 
%
top_goal_c pdd_test_times1_plus dist []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (y\ (app forall [nat,
      (abs (z\ (app eq [
       (app otimes [x, (app plus [y, z])]), 
       (app plus [(app otimes [x, y]), (app otimes [x, z])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_times1_plus, different argument order from dist
%
top_goal_c pdd_test_times1_plus distr []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (y\ (app eq [(app otimes [(app plus [y, z]), x]),
       (app plus [(app otimes [y, x]), (app otimes [z, x])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_times1_plus, different argument order from dist
%
top_goal_c pdd_test_times1_plus assm []
   (app forall [nat,
    (abs (z\ (app forall [nat,
     (abs (y\ (app forall [nat,
      (abs (x\ (app eq [
       (app otimes [(app otimes [x, y]), z]),
       (app otimes [x, (app otimes [y, z])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

top_goal_c pdd_test_times1_plus zerotimes []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app imp [(app or [
				(app eq [x, zero]),
				(app eq [y, zero])]),
			(app eq [(app otimes [x, y]), zero])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_times1_plus 
%

% simple pdd_test_times1_plus 
%
top_goal_c pdd_test_times1_plus dist []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (y\ (app forall [nat,
      (abs (z\ (app eq [
       (app otimes [x, (app plus [y, z])]), 
       (app plus [(app otimes [x, y]), (app otimes [x, z])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_times1_plus, different argument order from dist
%

top_goal_c pdd_test_times1_plus times2right []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app eq [(app otimes [x, (app s [y])]),
			(app plus [x, (app otimes [x, y])])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].


% exp
%
definition pdd_test_times1_plus exp1 trueP
   (app exp [_, zero]) 
   (app s [zero]).
definition pdd_test_times1_plus exp2 trueP
   (app exp [X, (app s [Y])]) 
   (app otimes [X, (app exp [X, Y])]).

% slightly more difficult pdd_test_times1_plus
%
top_goal_c pdd_test_times1_plus expplus []
    (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (x\ (app forall [nat,
       (abs (y\ (app eq [
        (app exp [x, (app plus [y, z])]),
        (app otimes [
         (app exp [x, y]), 
         (app exp [x, z])])])) nat)])) nat)])) nat)]) [(unsure exp [(rrstatus exp1 Tree [] Used), (rrstatus exp2 TreeA [] UsedA)]),
(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].
%% identifies incorrect rule.

% slightly more difficult pdd_test_times1_plus
%
top_goal_c pdd_test_times1_plus exptimes []
    (app forall [nat,
     (abs (n\ (app forall [nat,
      (abs (m\ (app forall [nat,
       (abs (o\ (app eq  [
        (app exp [o, (app otimes [m, n])]),
        (app exp [(app exp [o, m]), n])])) nat)])) nat)])) nat)]) 
[(unsure exp [(rrstatus exp1 Tree [] Used), (rrstatus exp2 TreeA [] UsedA)]),
(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].


% s_functional
%
lemma pdd_test_times1_plus s_functional equiv trueP
   (app eq [(app s [X]), (app s [Y])]) 
   (app eq [X, Y]).


%%
%% Constructor style schemes
%%


% Structural induction for naturals
%
induction_scheme pdd_test_times1_plus nat_struct
   nat
   (dom (a \ (repl a (app s [a]))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall [nat, (abs Prop nat)])) Context)
   % Step case
   (
    ((allGoal nat z\ (seqGoal ((hyp (otype_of z nat) nha)::(hyp (Prop z) ind_hyp)::H >>> (Prop (app s [z]))) Context)))
   % Base case
    **
	(seqGoal (H >>> (Prop zero)) Context)
	).

induction_scheme pdd_test_times1_plus twostep
   nat
   (dom (a\ (repl a (app s [(app s [a])]))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall [nat, (abs Prop nat)])) Context)
   % Step cases
   (
    (allGoal nat n\ (seqGoal (((hyp (otype_of n nat) nha)::
                               (hyp (Prop n) ind_hyp)::H)
			   >>>
			   (Prop (app s [(app s [n])]))) Context))
   % Base case
    **
	( (seqGoal (H >>> (Prop zero)) Context) **
       (seqGoal (H >>> (Prop (app s [zero]))) Context))
	).



%% Pretty printing

prettify_special zero (str "0").
benchmark_plan pdd_test_times1_plus Meth Query :-
	       testloop (%interaction_mode command,
	       (set_theory_induction_scheme_list pdd_test_times1_plus,
	       (set_sym_eval_list [and3, and4, idty, s_functional, pdd_leq1, pdd_leq_ss, assAnd1, prop3, prop4, prop5, prop6, andlem, mono_fun_1, mono_fun_2],
		(add_theory_defs_to_sym_eval_list pdd_test_times1_plus,
	       (set_wave_rule_to_sym_eval,
	       (add_to_sym_eval_list [beta_reduction],
	       pds_plan Meth Query)))))).

end

