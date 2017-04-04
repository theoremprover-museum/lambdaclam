/*

File: arithmetic.mod
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2000

*/

%% Results
%% simple - correct.
%% assp - correct.
%% comp - correct.
%% plus2right - correct.
%% plus1lem - true.
%% plusxx - true.
%% zeroplus - confused by implications and falsity.
%% comm - changes times1 to times(0, X) = X.
%% dist - changes times1 to times(0, X) = X.
%% distr - true.
%% assm - true.
%% zerotimes - requirement to check instantiation in rewrite_with_hyp causing
%%   trouble.
%% times2right - correct
%% expplus - fingers exp1 then heap overflow.
%% exptimes -

module pdd_test_plus1.

accumulate pdd_repair.
accumulate constructive_logic.

local ptadummy osyn -> o.
ptadummy X.
/*
local ptadummy2 osyn -> o.
ptadummy2 X.
local ptadummy3 osyn -> o.
ptadummy3 X.
*/

/* SYNTAX CONSTANTS */

is_otype pdd_test_plus1 nat [zero] [s].

has_otype pdd_test_plus1 zero nat.
has_otype pdd_test_plus1 s (arrow [nat] nat).
has_otype pdd_test_plus1 plus (arrow [nat, nat] nat).
has_otype pdd_test_plus1 otimes (arrow [nat, nat] nat).
has_otype pdd_test_plus1 exp (arrow [nat, nat] nat).

known_false (app eq [zero, (app s [X])]).
known_false (app eq [(app s [X]), zero]).

% Basic rewrites
%

lemma pdd_test_plus1 neq_zero_s equiv trueP (app eq [zero, (app s _)]) 
                                        falseP.
lemma pdd_test_plus1 neq_s_zero equiv trueP (app eq [(app s _), zero]) 
                                        falseP.
lemma pdd_test_plus1 neq_eq equiv trueP (app neq [X, X]) falseP.


% plus
%
definition pdd_test_plus1 plus1 trueP (app plus [zero, Y]) (app s [zero]).
definition pdd_test_plus1 plus2 trueP
     (app plus [(app s [Y]), X]) 
     (app s [(app plus [Y, X])]).

top_goal_c pdd_test_plus1 simple [] (app eq [zero, (app plus [zero, (app plus [zero,  zero])])]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_plus1 
%
top_goal_c pdd_test_plus1 assp []
    (app forall [nat, 
     (abs (z\ (app forall [nat, 
      (abs (y\ (app forall [nat, 
       (abs (x\ (app eq [
        (app plus [(app plus [x, y]), z]), 
        (app plus [x, (app plus [y, z])])])) nat)])) nat)])) nat)]) [(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_plus1 
%
top_goal_c pdd_test_plus1 comp []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app plus [y, x]), (app plus [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus1 plus2right []
	(app forall [nat,
         (abs (y\ (app forall [nat,
	  (abs (x\ (app eq [
           (app plus [x, (app s [y])]),
           (app s [(app plus [x, y])])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus1 plus1lem []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [x, (app s [zero])]),
			(app s [x])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus1 plusxx []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [(app s [x]), x]),
			(app s [(app plus [x, x])])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_plus1 zeroplus []
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
definition pdd_test_plus1 times1 trueP
   (app otimes [zero, X]) 
   zero.
definition pdd_test_plus1 times2 trueP
   (app otimes [(app s [Y]), X]) 
   (app plus [(app otimes [Y, X]), X]).

% simple pdd_test_plus1 
%
top_goal_c pdd_test_plus1 comm []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app otimes [y, x]), (app otimes [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_plus1 
%

% simple pdd_test_plus1 
%
top_goal_c pdd_test_plus1 dist []
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

% simple pdd_test_plus1, different argument order from dist
%
top_goal_c pdd_test_plus1 distr []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (y\ (app eq [(app otimes [(app plus [y, z]), x]),
       (app plus [(app otimes [y, x]), (app otimes [z, x])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_plus1, different argument order from dist
%
top_goal_c pdd_test_plus1 assm []
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

top_goal_c pdd_test_plus1 zerotimes []
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

top_goal_c pdd_test_plus1 dist []
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

% simple pdd_test_plus1, different argument order from dist
%

top_goal_c pdd_test_plus1 times2right []
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
definition pdd_test_plus1 exp1 trueP
   (app exp [_, zero]) 
   (app s [zero]).
definition pdd_test_plus1 exp2 trueP
   (app exp [X, (app s [Y])]) 
   (app otimes [X, (app exp [X, Y])]).

% slightly more difficult pdd_test_plus1
%
top_goal_c pdd_test_plus1 expplus []
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

% slightly more difficult pdd_test_plus1
%
top_goal_c pdd_test_plus1 exptimes []
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
lemma pdd_test_plus1 s_functional equiv trueP
   (app eq [(app s [X]), (app s [Y])]) 
   (app eq [X, Y]).


%%
%% Constructor style schemes
%%


% Structural induction for naturals
%
induction_scheme pdd_test_plus1 nat_struct
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

induction_scheme pdd_test_plus1 twostep
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
benchmark_plan pdd_test_plus1 Meth Query :-
	       testloop (%interaction_mode command,
	       (set_theory_induction_scheme_list pdd_test_plus1,
	       (set_sym_eval_list [and3, and4, idty, s_functional, assAnd1, prop3, prop4, prop5, prop6, andlem],
		(add_theory_defs_to_sym_eval_list pdd_test_plus1,
	       (set_wave_rule_to_sym_eval,
	       (add_to_sym_eval_list [beta_reduction],
	       pds_plan Meth Query)))))).

end

