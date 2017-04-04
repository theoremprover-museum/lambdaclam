/*

File: arithmetic.mod
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2000

*/

module pdd_test_arith.

accumulate pdd_repair.
accumulate constructive_logic.

local ptadummy osyn -> o.
ptadummy X.
local ptadummy2 osyn -> o.
ptadummy2 X.
/*
local ptadummy3 osyn -> o.
ptadummy3 X.
*/

/* SYNTAX CONSTANTS */

is_otype pdd_test_arith nat [zero] [s].

has_otype pdd_test_arith zero nat.
has_otype pdd_test_arith s (arrow [nat] nat).
has_otype pdd_test_arith plus (arrow [nat, nat] nat).
has_otype pdd_test_arith minus (arrow [nat, nat] nat).
has_otype pdd_test_arith otimes (arrow [nat, nat] nat).
has_otype pdd_test_arith exp (arrow [nat, nat] nat).
has_otype pdd_test_arith pdd_leq (arrow [nat, nat] bool).
has_otype pdd_test_arith half (arrow [nat] nat).
has_otype pdd_test_arith double (arrow [nat] nat).
has_otype pdd_test_arith even (arrow [nat] bool).

injective_right plus _.
injective_left plus _.

injective_right otimes X :- not (X = zero).
injective_left otimes X:- not (X = zero).

injective_right exp _.
injective_left exp X:- not (X = zero).

lemma arithmetic mono_fun_1 equiv trueP 
(app eq [(app F [X, Y]), (app F [X, Z])]) 
(app eq [Y, Z]):-
     injective_right F X.

lemma arithmetic mono_fun_2 equiv trueP 
(app eq [(app F [Y, X]), (app F [Z, X])]) 
(app eq [Y, Z]):-
     injective_left F X.




has_otype pdd_test_arith pred (arrow [nat] nat).
definition pdd_test_arith pred1
	trueP
	(app pred [zero])
	zero.
definition pdd_test_arith pred2
	trueP
	(app pred [(app s [X])])
	X.

known_false (app eq [zero, (app s [X])]).
known_false (app eq [(app s [X]), zero]).

% Basic rewrites
%

lemma pdd_test_arith neq_zero_s equiv trueP (app eq [zero, (app s _)]) 
                                        falseP.
lemma pdd_test_arith neq_s_zero equiv trueP (app eq [(app s _), zero]) 
                                        falseP.
lemma pdd_test_arith neq_eq equiv trueP (app neq [X, X]) falseP.


%% Results missing base case 
%% simple - no rewrites at all base case ground
%% assp - finds and corrects error
%% comp - starts trying to synthesize 
%% (plus (<lc-0-4>, s (X) = Y (<lc-0-4>, s (Z)))
%% plus2right - missing step rule
%% plus1lem - missing rewrite plusright
%% plusxx - base case rewrite not used
%% zeroplus - evaluate gets in invoked after rewrite_with_hyp then strange
%% things happen


%% Incorrect base case ... = 1
%% simple - no rewrites at all base case ground
%% assp - finds and corrects error
%% comp - starts trying to synthesize 
%% (plus (<lc-0-4>, s (X) = Y (<lc-0-4>, s (Z)))
%% plus2right - missing rule
%% plus1lem - missing rewrite plusright
%% plusxx - 
%% zeroplus - 

%% Incorrect step case ... = s(s(plus(x, y))
%% simple - step case not invoked.
%% assp - fingers plus1 since step case true...
%% comp - starts trying to synthesize 
%% (plus (<lc-0-4>, s (X) = Y (<lc-0-4>, s (Z)))
%% plus2right - missing rule

%% Incorrect base case ... = 1 (no missing case)
%% simple - no rewrites at all base case ground
%% assp - finds and corrects error
%% comp - finds and correxts error
%% plus2right - finds and corrects error
%% plus1lem - theorem true.
%% plusxx - doesn't use base case.
%% zeroplus - evaluate gets in invoked after rewrite_with_hyp then strange
%% things happen

%% Incorrect step case ... = s(s(plus(x, y)) (no missing case)
%% simple -  true.
%% assp - fingers plus1. step case plus2 - second indudction step case true, base case false
%%      - need to check base case as well for full score!!!
%% comp - fingers plus1.
%% plus2right - true.
%% plus1lem - finds and correxts error.
%% plusxx - fingers plus2 but then can't instantiate rule properly because
%%        - congr doesn't check other unifiers.
%% zeroplus - theorem true.


% plus
%
definition pdd_test_arith plus1 trueP (app plus [zero, Y]) Y.
definition pdd_test_arith plus2 trueP
     (app plus [(app s [Y]), X]) 
     (app s [(app plus [Y, X])]).

top_goal_c pdd_test_arith simple [] (app eq [zero, (app plus [zero, (app plus [zero,  zero])])]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_arith 
%
top_goal_c pdd_test_arith assp []
    (app forall [nat, 
     (abs (z\ (app forall [nat, 
      (abs (y\ (app forall [nat, 
       (abs (x\ (app eq [
        (app plus [(app plus [x, y]), z]), 
        (app plus [x, (app plus [y, z])])])) nat)])) nat)])) nat)]) [(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_test_arith 
%
top_goal_c pdd_test_arith comp []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app plus [y, x]), (app plus [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_arith plus2right []
	(app forall [nat,
         (abs (y\ (app forall [nat,
	  (abs (x\ (app eq [
           (app plus [x, (app s [y])]),
           (app s [(app plus [x, y])])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_arith plus1lem []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [x, (app s [zero])]),
			(app s [x])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_arith plusxx []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [(app s [x]), x]),
			(app s [(app plus [x, x])])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_test_arith zeroplus []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app imp [(app and [
				(app eq [x, zero]),
				(app eq [y, zero])]),
			(app eq [(app plus [x, y]), zero])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].


%% Results missing base case (plus)
%% comm - 
%% dist - 
%% distr - 
%% assm -
%% zerotimes - 
%% times2right - 

%% Incorrect base case (plus) ... = 1 (no missing case)
%% comm - 
%% dist - 
%% distr - 
%% assm - 
%% zerotimes - 
%% times2right - 

%% Incorrect step case (plus) ... = s(s(plus(x, y))
%% comm - 
%% dist - 
%% distr - 
%% assm - 
%% zerotimes - 
%% times2right - 

%% Results missing base case (times)

%% Incorrect base case (times) ... = X (no missing case)
%% comm -  reaches s(0) = 0 but critic doesn't fire
%% dist - theorem true.
%% distr -ripple analysis wrong?
%% assm - ripple analysis wrong?
%% zerotimes - s(0) = 0
%% times2right - picks on plus2

%% Incorrect base case (times) ... = plus(X, X)

%% Incorrect step case (times) ... = s(times(Y, X))

%% Incorrect step case (times) ... = plus(times(Y, X), Y)


% times
%
definition pdd_test_arith times1 trueP
   (app otimes [zero, X]) 
   zero.
definition pdd_test_arith times2 trueP
   (app otimes [(app s [Y]), X]) 
   (app plus [(app otimes [Y, X]), X]).

% simple pdd_test_arith 
%
top_goal_c pdd_test_arith comm []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app otimes [y, x]), (app otimes [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_arith 
%

% simple pdd_test_arith 
%
top_goal_c pdd_test_arith dist []
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

% simple pdd_test_arith, different argument order from dist
%
top_goal_c pdd_test_arith distr []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (y\ (app eq [(app otimes [(app plus [y, z]), x]),
       (app plus [(app otimes [y, x]), (app otimes [z, x])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_test_arith, different argument order from dist
%
top_goal_c pdd_test_arith assm []
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

top_goal_c pdd_test_arith zerotimes []
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

% simple pdd_test_arith 
%

% simple pdd_test_arith 
%
top_goal_c pdd_test_arith dist []
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

% simple pdd_test_arith, different argument order from dist
%

top_goal_c pdd_test_arith times2right []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app eq [(app otimes [x, (app s [y])]),
			(app plus [x, (app otimes [x, y])])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].


%% missing base case (plus)

%% Incorrect base case (plus) ... = 1 (no missing case)
%% expplus - picks exp1 as incorrect
%% exptimes - picks exp2 as incorrect

%% Incorrect base case (times) ... = X (no missing case)

%% incorrect step case (plus)

%% Incorrect base case (exp) ... = 0

%% Incorrect base case (exp) ... = plus(X, X)

%% Incorect step case (exp) = plus (X, exp (X, Y))

% exp
%
definition pdd_test_arith exp1 trueP
   (app exp [_, zero]) 
   (app s [zero]).
definition pdd_test_arith exp2 trueP
   (app exp [X, (app s [Y])]) 
   (app otimes [X, (app exp [X, Y])]).

% slightly more difficult pdd_test_arith
%
top_goal_c pdd_test_arith expplus []
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

% slightly more difficult pdd_test_arith
%
top_goal_c pdd_test_arith exptimes []
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
lemma pdd_test_arith s_functional equiv trueP
   (app eq [(app s [X]), (app s [Y])]) 
   (app eq [X, Y]).

% pdd_leq
%
% also not clear on definition/lemma distinction here
axiom pdd_test_arith pdd_leq1 equiv trueP
   (app pdd_leq [zero, Y])
   falseP.
axiom pdd_test_arith pdd_leq_ss equiv trueP
   (app pdd_leq  [(app s [X]), (app s [Y])]) 
   (app pdd_leq [X, Y]).
lemma pdd_test_arith pdd_leq_transitive equiv 
	trueP
	(app transitive [pdd_leq])
	trueP.

%% missing base case (leq)
%% leqrefl - locates missing rule, but not rewriting in hypothesis
%% leqsuc - wrong missing rule
%% leqsum - wrong missing rule

%% incorrect base case (leq) = false - no missing case

% For some reason called notpdd_leqreflex in CLAM corpus
%
top_goal_c pdd_test_arith pdd_leqrefl []
   (app forall [nat,
    (abs (n\ (app pdd_leq [n, n])) nat)])
     [(unsure pdd_leq [(rrstatus pdd_leq1 Tree [] Used), (rrstatus pdd_leq_ss Tree2 [] Used2)])]
.

% Arithmetic.
%
top_goal_c pdd_test_arith pdd_leqsuc  []
    (app forall [nat,
       (abs (n\ (app pdd_leq [n, (app s [n])])) nat)]) 
     [(unsure pdd_leq [(rrstatus pdd_leq1 Tree [] Used), (rrstatus pdd_leq_ss Tree2 [] Used2)])]
.


top_goal_c pdd_test_arith pdd_leqsum []
      (app forall [nat,
                (abs (alpha\ (app forall [nat,
        (abs (beta\ (app pdd_leq [alpha, (app plus [beta, alpha])])) nat)])) nat)])
     [(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure pdd_leq [(rrstatus pdd_leq1 Tree [] Used), (rrstatus pdd_leq_ss TreeA [] UsedA)])]
.

%% missing base case
% doubleplus - wrong missing rule.
% doubletimes -
% doubletimes2 -

%% incorrect base case (double) = 1 - no missing case

definition pdd_test_arith double1 trueP
   (app double [zero])
   (app s [zero]).

definition pdd_test_arith double2 trueP
(app double [(app s [X])])
(app s [(app double [X])]).

top_goal_c pdd_test_arith doubleplus []
	(app forall [nat, (abs (x\
		(app eq [(app double [x]),
				(app plus [x, x])])) nat)])
     [(unsure double [(rrstatus double1 Tree [] Used), (rrstatus double2 TreeA [] UsedA)]),
(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])]
.

top_goal_c pdd_test_arith doubletimes []
	(app forall [nat, (abs (x\
		(app eq [(app double [x]),
				(app otimes [(app s [(app s [zero])]), x])])) nat)])
     [(unsure double [(rrstatus double1 Tree [] Used), (rrstatus double2 TreeA [] UsedA)]),
(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])]
.

top_goal_c pdd_test_arith doubletimes2 []
	  (app forall [nat, (abs (x\
                (app eq [(app double [x]),
                                (app otimes [x, (app s [(app s [zero])])])])) nat)])
     [(unsure double [(rrstatus double1 Tree [] Used), (rrstatus double2 TreeA [] UsedA)]), 
(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])]
.

%%
%% Constructor style schemes
%%


% Structural induction for naturals
%
induction_scheme pdd_test_arith nat_struct
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

induction_scheme pdd_test_arith twostep
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
benchmark_plan pdd_test_arith Meth Query :-
	       testloop (%interaction_mode command,
	       (set_theory_induction_scheme_list pdd_test_arith,
	       (set_sym_eval_list [and3, and4, idty, s_functional, pdd_leq1, pdd_leq_ss, assAnd1, prop3, prop4, prop5, prop6, andlem, mono_fun_1, mono_fun_2],
		(add_theory_defs_to_sym_eval_list pdd_test_arith,
	       (set_wave_rule_to_sym_eval,
	       (add_to_sym_eval_list [beta_reduction],
	       pds_plan Meth Query)))))).

end

