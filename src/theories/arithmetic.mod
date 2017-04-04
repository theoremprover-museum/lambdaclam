/*

File: arithmetic.mod
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2000

*/

module arithmetic.

accumulate lclam.

/* SYNTAX CONSTANTS */

is_otype arithmetic nat [zero] [s].

has_otype arithmetic zero nat.
has_otype arithmetic s (arrow [nat] nat).
has_otype arithmetic plus (arrow [nat, nat] nat).
has_otype arithmetic minus (arrow [nat, nat] nat).
has_otype arithmetic otimes (arrow [nat, nat] nat).
has_otype arithmetic exp (arrow [nat, nat] nat).
has_otype arithmetic leq (arrow [nat, nat] bool).
has_otype arithmetic half (arrow [nat] nat).
has_otype arithmetic double (arrow [nat] nat).
has_otype arithmetic even (arrow [nat] bool).
has_otype arithmetic fun_compose (arrow [(arrow [B] A), (arrow [A] C)] (arrow [B] C)).
has_otype arithmetic fun_iter (arrow [nat, (arrow [A] A)] (arrow [A] A)).

injective_right plus _.
injective_left plus _.

injective_right otimes X:- not (X = zero).
injective_left otimes X:- not (X = zero).

injective_right exp _.
injective_left exp Y:- not (Y = zero).

has_otype arithmetic pred (arrow [nat] nat).
definition arithmetic pred1
	trueP
	(app pred [zero])
	zero.
definition arithmetic pred2
	trueP
	(app pred [(app s [X])])
	X.

% Basic rewrites
%

lemma arithmetic neq_zero_s equiv trueP (app eq [zero, (app s _)]) 
                                        falseP.
lemma arithmetic neq_s_zero equiv trueP (app eq [(app s _), zero]) 
                                        falseP.
lemma arithmetic neq_eq equiv trueP (app neq [X, X]) falseP.


% plus
%
definition arithmetic plus1 trueP (app plus [zero, Y]) Y.
definition arithmetic plus2 trueP
     (app plus [(app s [Y]), X]) 
     (app s [(app plus [Y, X])]).


% times
%
definition arithmetic times1 trueP
   (app otimes [zero, _]) 
   zero.
definition arithmetic times2 trueP
   (app otimes [(app s [Y]), X]) 
   (app plus [(app otimes [Y, X]), X]).

% exp
%
definition arithmetic exp1 trueP
   (app exp [_, zero]) 
   (app s [zero]).
definition arithmetic exp2 trueP
   (app exp [X, (app s [Y])]) 
   (app otimes [X, (app exp [X, Y])]).

% s_functional
%
lemma arithmetic s_functional equiv trueP
   (app eq [(app s [X]), (app s [Y])]) 
   (app eq [X, Y]).

lemma arithmetic mono_fun_1 equiv trueP 
(app eq [(app F [X, Y]), (app F [X, Z])]) 
(app eq [Y, Z]):-
     injective_right F X.

lemma arithmetic mono_fun_2 equiv trueP 
(app eq [(app F [Y, X]), (app F [Z, X])]) 
(app eq [Y, Z]):-
     injective_left F X.



% leq
%
% also not clear on definition/lemma distinction here
axiom arithmetic leq1 equiv trueP
   (app leq [zero, _Y])
   trueP.
axiom arithmetic leq2 equiv trueP
   (app leq [(app s _), zero])
   falseP.
axiom arithmetic leq_ss equiv trueP
   (app leq  [(app s [X]), (app s [Y])]) 
   (app leq [X, Y]).
lemma arithmetic leq_transitive equiv 
	trueP
	(app transitive [leq])
	trueP.

% half
%
definition arithmetic half1 trueP
(app half [zero])
zero.

definition arithmetic half2 trueP
(app half [(app s [zero])])
(app s [zero]).

definition arithmetic half3 trueP
(app half [(app s [(app s [X])])])
(app s [(app half [X])]).

% double
%
definition arithmetic double1 trueP
(app double [zero])
zero.

definition arithmetic double2 trueP
(app double [(app s [X])])
(app s [(app s [(app double [X])])]).

% even
%
definition arithmetic even1 trueP
(app even [zero])
trueP.

definition arithmetic even2 trueP
(app even [(app s [zero])])
falseP.

definition arithmetic even3 trueP
(app even [(app s [(app s [X])])])
(app even [X]).

definition arithmetic fun_iter1 
	trueP
	(app fun_iter [zero, F])
	(abs (x\ x) _).
definition arithmetic fun_iter2
	trueP
	(app F [(app (app fun_iter [N, F]) [Z])])
	(app (app fun_iter [(app s [N]), F]) [Z]).
definition arithmetic fun_iter3
	trueP
	(app F [(app (app fun_iter [N, (abs (x\ (app F [x])) _)]) [Z])])
	(app (app fun_iter [(app s [N]), (abs (x\ (app F [x])) _)]) [Z]).

axiom arithmetic fun_compose1 equiv
	trueP
	(app (app fun_compose [F, G]) [X])
	(app F [(app G [X])]).
bad_for_synthesis fun_compose1 (app F _):-
        headvar_osyn F.


has_otype arithmetic less (arrow [nat, nat] bool).
axiom arithmetic less1 equiv
	trueP
	(app less [X, zero])
	falseP.
axiom arithmetic less2 equiv
	trueP
	(app less [zero, (app s [X])])
	trueP.
axiom arithmetic less3 equiv
	trueP
	(app less [(app s [X]), (app s [Y])])
	(app less [X, Y]).
lemma arithmetic less_transitive equiv 
        trueP
        (app transitive [less])
        trueP.


%%
%% Constructor style schemes
%%


% Structural induction for naturals
%
induction_scheme arithmetic nat_struct
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

induction_scheme arithmetic twostep
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

% simple tautology
%
top_goal arithmetic eqzero [] (app eq [zero, zero]).
% simple tautology
%
top_goal arithmetic simple [] (app eq [zero, (app plus [zero, (app plus [zero,  zero])])]).

% simple tautology
%
top_goal arithmetic simple_taut [] (app imp [(app eq [zero, zero]), (app eq [zero, zero])]).

% simple arithmetic 
%
top_goal arithmetic assp []
    (app forall [nat, 
     (abs (z\ (app forall [nat, 
      (abs (y\ (app forall [nat, 
       (abs (x\ (app eq [
        (app plus [(app plus [x, y]), z]), 
        (app plus [x, (app plus [y, z])])])) nat)])) nat)])) nat)]).

% simple arithmetic 
%
top_goal arithmetic comp []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app plus [y, x]), (app plus [x, y])])) nat)])) nat)]).

% simple arithmetic 
%
top_goal arithmetic comm []
     (app forall [nat,
      (abs (x\ (app forall [nat, 
       (abs (y\ (app eq [(app otimes [y, x]), (app otimes [x, y])])) nat)])) nat)]).

% simple arithmetic, false
%
top_goal arithmetic falsearith []
	(app forall [nat, (abs (x\ (app eq  [x, (app s [x])])) nat)]).

% simple arithmetic 
%
top_goal arithmetic plus2right []
	(app forall [nat,
         (abs (y\ (app forall [nat,
	  (abs (x\ (app eq [
           (app plus [x, (app s [y])]),
           (app s [(app plus [x, y])])])) nat)])) nat)]).

% simple arithmetic 
%
top_goal arithmetic dist []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (y\ (app forall [nat,
      (abs (z\ (app eq [
       (app otimes [x, (app plus [y, z])]), 
       (app plus [(app otimes [x, y]), (app otimes [x, z])])])) nat)])) nat)])) nat)]).

% simple arithmetic, different argument order from dist
%
top_goal arithmetic distr []
   (app forall [nat,
    (abs (x\ (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (y\ (app eq [(app otimes [(app plus [y, z]), x]),
       (app plus [(app otimes [y, x]), (app otimes [z, x])])])) nat)])) nat)])) nat)]).

% simple arithmetic, different argument order from dist
%
top_goal arithmetic assm []
   (app forall [nat,
    (abs (z\ (app forall [nat,
     (abs (y\ (app forall [nat,
      (abs (x\ (app eq [
       (app otimes [(app otimes [x, y]), z]),
       (app otimes [x, (app otimes [y, z])])])) nat)])) nat)])) nat)]).

% simple arithmetic synthesis proof, meta-variable for synthesised function.
%
top_goal arithmetic assp_sy []
     (app forall [nat,
      (abs (x\ (app forall [nat,
       (abs (y\ (app forall [nat,
        (abs (z\ (app eq [
         (app plus [(app plus [x, y]), z]),  
         (app plus [x, (app W [x, y, z])])])) nat)])) nat)])) nat)]).

% slightly more difficult arithmetic
%
top_goal arithmetic expplus []
    (app forall [nat,
     (abs (z\ (app forall [nat,
      (abs (x\ (app forall [nat,
       (abs (y\ (app eq [
        (app exp [x, (app plus [y, z])]),
        (app otimes [
         (app exp [x, y]), 
         (app exp [x, z])])])) nat)])) nat)])) nat)]).

% slightly more difficult arithmetic
%
top_goal arithmetic exptimes []
    (app forall [nat,
     (abs (n\ (app forall [nat,
      (abs (m\ (app forall [nat,
       (abs (o\ (app eq  [
        (app exp [o, (app otimes [m, n])]),
        (app exp [(app exp [o, m]), n])])) nat)])) nat)])) nat)]).

% For some reason called notleqreflex in CLAM corpus
%
top_goal arithmetic leqrefl []
   (app forall [nat,
    (abs (n\ (app leq [n, n])) nat)]).

% Arithmetic.
%
top_goal arithmetic leqsuc  []
    (app forall [nat,
       (abs (n\ (app leq [n, (app s [n])])) nat)]).


top_goal arithmetic leqsum []
      (app forall [nat,
                (abs (alpha\ (app forall [nat,
        (abs (beta\ (app leq [alpha, (app plus [beta, alpha])])) nat)])) nat)]).

top_goal arithmetic doublehalf []
	(app forall [nat, (abs (x\
		(app eq [(app double [(app half [x])]),
			x])) nat)]).

top_goal arithmetic halfdouble []
	(app forall [nat, (abs (x\
		(app eq [
			(app half [(app double [x])]),
			x])) nat)]).

top_goal arithmetic halfplus []
	(app forall [nat, (abs (x\
		(app eq [
			(app half [(app plus [x, x])]),
			x])) nat)]).

top_goal arithmetic plus1lem []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [x, (app s [zero])]),
			(app s [x])])) nat)]).

top_goal arithmetic plusxx []
	(app forall [nat, (abs (x\
		(app eq [
			(app plus [(app s [x]), x]),
			(app s [(app plus [x, x])])])) nat)]).

top_goal arithmetic zeroplus []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app imp [(app and [
				(app eq [x, zero]),
				(app eq [y, zero])]),
			(app eq [(app plus [x, y]), zero])])) nat)])) nat)]).

top_goal arithmetic zerotimes []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app imp [(app or [
				(app eq [x, zero]),
				(app eq [y, zero])]),
			(app eq [(app otimes [x, y]), zero])])) nat)])) nat)]).

top_goal arithmetic doubleplus []
	(app forall [nat, (abs (x\
		(app eq [(app double [x]),
				(app plus [x, x])])) nat)]).

top_goal arithmetic doubletimes []
	(app forall [nat, (abs (x\
		(app eq [(app double [x]),
				(app otimes [(app s [(app s [zero])]), x])])) nat)]).

top_goal arithmetic times2right []
	(app forall [nat, (abs (x\
		(app forall [nat, (abs (y\
	(app eq [(app otimes [x, (app s [y])]),
			(app plus [x, (app otimes [x, y])])])) nat)])) nat)]).

top_goal arithmetic doubletimes2 []
	  (app forall [nat, (abs (x\
                (app eq [(app double [x]),
                                (app otimes [x, (app s [(app s [zero])])])])) nat)]).

%% Pretty printing

prettify_special zero (str "0").

end

