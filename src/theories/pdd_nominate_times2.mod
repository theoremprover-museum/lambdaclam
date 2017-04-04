/*

File: times2metic.mod
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2000

*/

module pdd_nominate_times2.

accumulate pdd_nominate.
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
%% comm - times1 heap overflow
%% dist - plus1 heap overflow
%% distr - plus1 - evalute hangs
%% assm - plus1 -
%% zerotimes - loops
%% times2right - plus2
%% expplus - exp2
%% exptimes -

injective_right plus _.
injective_left plus _.

injective_right otimes X:- not (X = zero).
injective_left otimes X:- not (X = zero).

injective_right exp _.
injective_left exp Y:- not (Y = zero).


is_otype pdd_nominate_times2 nat [zero] [s].

has_otype pdd_nominate_times2 zero nat.
has_otype pdd_nominate_times2 s (arrow [nat] nat).
has_otype pdd_nominate_times2 plus (arrow [nat, nat] nat).
has_otype pdd_nominate_times2 minus (arrow [nat, nat] nat).
has_otype pdd_nominate_times2 otimes (arrow [nat, nat] nat).
has_otype pdd_nominate_times2 exp (arrow [nat, nat] nat).
has_otype pdd_nominate_times2 pdd_leq (arrow [nat, nat] bool).
has_otype pdd_nominate_times2 half (arrow [nat] nat).
has_otype pdd_nominate_times2 double (arrow [nat] nat).
has_otype pdd_nominate_times2 even (arrow [nat] bool).

lemma arithmetic mono_fun_1 equiv trueP 
(app eq [(app F [X, Y]), (app F [X, Z])]) 
(app eq [Y, Z]):-
     injective_right F X.

lemma arithmetic mono_fun_2 equiv trueP 
(app eq [(app F [Y, X]), (app F [Z, X])]) 
(app eq [Y, Z]):-
     injective_left F X.




has_otype pdd_nominate_times2 pred (arrow [nat] nat).
definition pdd_nominate_times2 pred1
	trueP
	(app pred [zero])
	zero.
definition pdd_nominate_times2 pred2
	trueP
	(app pred [(app s [X])])
	X.

known_false (app eq [zero, (app s [X])]) _.
known_false (app eq [(app s [X]), zero]) _.

% Basic rewrites
%

lemma pdd_nominate_times2 neq_zero_s equiv trueP (app eq [zero, (app s _)]) 
                                        falseP.
lemma pdd_nominate_times2 neq_s_zero equiv trueP (app eq [(app s _), zero]) 
                                        falseP.
lemma pdd_nominate_times2 neq_eq equiv trueP (app neq [X, X]) falseP.


% plus
%
definition pdd_nominate_times2 plus1 trueP (app plus [zero, Y]) Y.
definition pdd_nominate_times2 plus2 trueP
     (app plus [(app s [Y]), X]) 
     (app s [(app plus [Y, X])]).

top_goal_c pdd_nominate_times2 simple [] (app eq [zero, (app plus [zero, (app plus [zero,  zero])])]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_nominate_times2 
%
top_goal_c pdd_nominate_times2 assp []
    (app forall [nat, 
     (abs (z\ (app forall [nat, 
      (abs (y\ (app forall [nat, 
       (abs (x\ (app eq [
        (app plus [(app plus [x, y]), z]), 
        (app plus [x, (app plus [y, z])])])) nat)])) nat)])) nat)]) [(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

% simple pdd_nominate_times2 
%
top_goal_c pdd_nominate_times2 comp []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app plus [y, x]), (app plus [x, y])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_nominate_times2 plus2right []
	(app forall [nat,
         (abs (y\ (app forall [nat,
	  (abs (x\ (app eq [
           (app plus [x, (app s [y])]),
           (app s [(app plus [x, y])])])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_nominate_times2 plus1lem []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [x, (app s [zero])]),
			(app s [x])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_nominate_times2 plusxx []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [(app s [x]), x]),
			(app s [(app plus [x, x])])])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)])].

top_goal_c pdd_nominate_times2 zeroplus []
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
definition pdd_nominate_times2 pdd_times1 trueP
   (app otimes [zero, X]) 
   zero.
definition pdd_nominate_times2 pdd_times2 trueP
   (app otimes [(app s [Y]), X]) 
   (app plus [(app otimes [Y, X]), Y]).

% simple pdd_nominate_times2 
%
top_goal_c pdd_nominate_times2 comm2 []
     (app and [(app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app otimes [y, x]), (app otimes [x, y])])) nat)])) nat)]), diagnose])
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus pdd_times1 Tree3 [] Used3), 
               (rrstatus pdd_times2 Tree4 [] Used4)]),
(banned [times1, times2])
].

% simple pdd_nominate_times2 
%

% simple pdd_nominate_times2 
%
top_goal_c pdd_nominate_times2 dist []
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

% simple pdd_nominate_times2, different argument order from dist
%
top_goal_c pdd_nominate_times2 distr []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (y\ (app eq [(app otimes [(app plus [y, z]), x]),
       (app plus [(app otimes [y, x]), (app otimes [z, x])])])) nat)])) nat)])) nat)]) 
[(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])].

% simple pdd_nominate_times2, different argument order from dist
%
top_goal_c pdd_nominate_times2 assm []
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

top_goal_c pdd_nominate_times2 zerotimes []
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

% simple pdd_nominate_times2 
%

% simple pdd_nominate_times2 
%
top_goal_c pdd_nominate_times2 dist []
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

% simple pdd_nominate_times2, different argument order from dist
%

top_goal_c pdd_nominate_times2 times2right []
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
definition pdd_nominate_times2 exp1 trueP
   (app exp [_, zero]) 
   (app s [zero]).
definition pdd_nominate_times2 exp2 trueP
   (app exp [X, (app s [Y])]) 
   (app otimes [X, (app exp [X, Y])]).

% slightly more difficult pdd_nominate_times2
%
top_goal_c pdd_nominate_times2 expplus []
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

% slightly more difficult pdd_nominate_times2
%
top_goal_c pdd_nominate_times2 exptimes []
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
lemma pdd_nominate_times2 s_functional equiv trueP
   (app eq [(app s [X]), (app s [Y])]) 
   (app eq [X, Y]).

% pdd_leq
%
% also not clear on definition/lemma distinction here
axiom pdd_nominate_times2 pdd_leq1 equiv trueP
   (app pdd_leq [zero, Y])
   falseP.
axiom pdd_nominate_times2 pdd_leq_ss equiv trueP
   (app pdd_leq  [(app s [X]), (app s [Y])]) 
   (app pdd_leq [X, Y]).
lemma pdd_nominate_times2 pdd_leq_transitive equiv 
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
top_goal_c pdd_nominate_times2 pdd_leqrefl []
   (app forall [nat,
    (abs (n\ (app pdd_leq [n, n])) nat)])
     [(unsure pdd_leq [(rrstatus pdd_leq1 Tree [] Used), (rrstatus pdd_leq_ss Tree2 [] Used2)])]
.

% Arithmetic.
%
top_goal_c pdd_nominate_times2 pdd_leqsuc  []
    (app forall [nat,
       (abs (n\ (app pdd_leq [n, (app s [n])])) nat)]) 
     [(unsure pdd_leq [(rrstatus pdd_leq1 Tree [] Used), (rrstatus pdd_leq_ss Tree2 [] Used2)])]
.


top_goal_c pdd_nominate_times2 pdd_leqsum []
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

definition pdd_nominate_times2 double1 trueP
   (app double [zero])
   (app s [zero]).

definition pdd_nominate_times2 double2 trueP
(app double [(app s [X])])
(app s [(app double [X])]).

top_goal_c pdd_nominate_times2 doubleplus []
	(app forall [nat, (abs (x\
		(app eq [(app double [x]),
				(app plus [x, x])])) nat)])
     [(unsure double [(rrstatus double1 Tree [] Used), (rrstatus double2 TreeA [] UsedA)]),
(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])]
.

top_goal_c pdd_nominate_times2 doubletimes []
	(app forall [nat, (abs (x\
		(app eq [(app double [x]),
				(app otimes [(app s [(app s [zero])]), x])])) nat)])
     [(unsure double [(rrstatus double1 Tree [] Used), (rrstatus double2 TreeA [] UsedA)]),
(unsure plus [(rrstatus plus1 Tree1 [] Used1), 
               (rrstatus plus2 Tree2 [] Used2)]),
(unsure otimes [(rrstatus times1 Tree3 [] Used3), 
               (rrstatus times2 Tree4 [] Used4)])]
.

top_goal_c pdd_nominate_times2 doubletimes2 []
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
induction_scheme pdd_nominate_times2 nat_struct
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

induction_scheme pdd_nominate_times2 twostep
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
benchmark_plan pdd_nominate_times2 Meth Query :-
	       testloop (%interaction_mode command,
	       (set_theory_induction_scheme_list pdd_nominate_times2,
	       (set_sym_eval_list [and3, and4, idty, s_functional, pdd_leq1, pdd_leq_ss, assAnd1, prop3, prop4, prop5, prop6, andlem, mono_fun_1, mono_fun_2],
		(add_theory_defs_to_sym_eval_list pdd_nominate_times2,
	       (set_wave_rule_to_sym_eval,
	       (add_to_sym_eval_list [beta_reduction],
	       pds_plan Meth Query)))))).

end

