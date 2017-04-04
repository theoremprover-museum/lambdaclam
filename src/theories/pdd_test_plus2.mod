/*

File: arithmetic.mod
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2000

*/

module pdd_test_plus2.

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

/* SYNTAX CONSTANTS */

%% Results
%% simple - true.
%% assp - plus 2 = s(X) + Y = X + Y
%% comp - fingrs plus1.
%% plus2right - true.
%% plus1lem - correct.
%% plusxx - correct rule the bus error.
%% zeroplus - true.
%% comm - fingers plus1 heap overflo
%% dist - true.
%% distr - correct.
%% assm - fingers plus2 - instantiation fails.
%% zerotimes - true.
%% times2right - 
%% expplus - 
%% exptimes -


is_otype pdd_test_plus2 nat [zero] [s].

has_otype pdd_test_plus2 zero nat.
has_otype pdd_test_plus2 s (arrow [nat] nat).
has_otype pdd_test_plus2 plus (arrow [nat, nat] nat).
has_otype pdd_test_plus2 minus (arrow [nat, nat] nat).
has_otype pdd_test_plus2 otimes (arrow [nat, nat] nat).
has_otype pdd_test_plus2 exp (arrow [nat, nat] nat).
has_otype pdd_test_plus2 pdd_leq (arrow [nat, nat] bool).
has_otype pdd_test_plus2 half (arrow [nat] nat).
has_otype pdd_test_plus2 double (arrow [nat] nat).
has_otype pdd_test_plus2 even (arrow [nat] bool).

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




has_otype pdd_test_plus2 pred (arrow [nat] nat).
definition pdd_test_plus2 pred1
	trueP
	(app pred [zero])
	zero.
definition pdd_test_plus2 pred2
	trueP
	(app pred [(app s [X])])
	X.

known_false (app eq [zero, (app s [X])]).
known_false (app eq [(app s [X]), zero]).

% Basic rewrites
%

lemma pdd_test_plus2 neq_zero_s equiv trueP (app eq [zero, (app s _)]) 
                                        falseP.
lemma pdd_test_plus2 neq_s_zero equiv trueP (app eq [(app s _), zero]) 
                                        falseP.
lemma pdd_test_plus2 neq_eq equiv trueP (app neq [X, X]) falseP.

% plus
%
definition pdd_test_plus2 plus1 trueP (app plus [zero, Y]) Y.
definition pdd_test_plus2 plus2 trueP
     (app plus [(app s [Y]), X]) 
     (app s [(app s [(app plus [Y, X])])]).

top_goal_c pdd_test_plus2 simple [] (app eq [zero, (app plus [zero, (app plus [zero,  zero])])]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_plus2 
%
top_goal_c pdd_test_plus2 assp []
    (app forall [nat, 
     (abs (z\ (app forall [nat, 
      (abs (y\ (app forall [nat, 
       (abs (x\ (app eq [
        (app plus [(app plus [x, y]), z]), 
        (app plus [x, (app plus [y, z])])])) nat)])) nat)])) nat)]) [(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_plus2 
%
top_goal_c pdd_test_plus2 comp []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app plus [y, x]), (app plus [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus2 plus2right []
	(app forall [nat,
         (abs (y\ (app forall [nat,
	  (abs (x\ (app eq [
           (app plus [x, (app s [y])]),
           (app s [(app plus [x, y])])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus2 plus1lem []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [x, (app s [zero])]),
			(app s [x])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus2 plusxx []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [(app s [x]), x]),
			(app s [(app plus [x, x])])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus2 zeroplus []
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
definition pdd_test_plus2 times1 trueP
   (app otimes [zero, X]) 
   zero.
definition pdd_test_plus2 times2 trueP
   (app otimes [(app s [Y]), X]) 
   (app plus [(app otimes [Y, X]), X]).

% simple pdd_test_plus2 
%
top_goal_c pdd_test_plus2 comm []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app otimes [y, x]), (app otimes [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_plus2 
%

% simple pdd_test_plus2 
%
top_goal_c pdd_test_plus2 dist []
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

% simple pdd_test_plus2, different argument order from dist
%
top_goal_c pdd_test_plus2 distr []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (y\ (app eq [(app otimes [(app plus [y, z]), x]),
       (app plus [(app otimes [y, x]), (app otimes [z, x])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_plus2, different argument order from dist
%
top_goal_c pdd_test_plus2 assm []
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

top_goal_c pdd_test_plus2 zerotimes []
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

% simple pdd_test_plus2 
%

% simple pdd_test_plus2 
%
top_goal_c pdd_test_plus2 dist []
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

% simple pdd_test_plus2, different argument order from dist
%

top_goal_c pdd_test_plus2 times2right []
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
definition pdd_test_plus2 exp1 trueP
   (app exp [_, zero]) 
   (app s [zero]).
definition pdd_test_plus2 exp2 trueP
   (app exp [X, (app s [Y])]) 
   (app otimes [X, (app exp [X, Y])]).

% slightly more difficult pdd_test_plus2
%
top_goal_c pdd_test_plus2 expplus []
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

% slightly more difficult pdd_test_plus2
%
top_goal_c pdd_test_plus2 exptimes []
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
lemma pdd_test_plus2 s_functional equiv trueP
   (app eq [(app s [X]), (app s [Y])]) 
   (app eq [X, Y]).

%%
%% Constructor style schemes
%%


% Structural induction for naturals
%
induction_scheme pdd_test_plus2 nat_struct
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

induction_scheme pdd_test_plus2 twostep
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
benchmark_plan pdd_test_plus2 Meth Query :-
	       testloop (%interaction_mode command,
	       (set_theory_induction_scheme_list pdd_test_plus2,
	       (set_sym_eval_list [and3, and4, idty, s_functional, pdd_leq1, pdd_leq_ss, assAnd1, prop3, prop4, prop5, prop6, andlem, mono_fun_1, mono_fun_2],
		(add_theory_defs_to_sym_eval_list pdd_test_plus2,
	       (set_wave_rule_to_sym_eval,
	       (add_to_sym_eval_list [beta_reduction],
	       pds_plan Meth Query)))))).

end

