/*

File: ordl.mod
Author: Louise Dennis
Description: Ordinal Theory
Last Modified: 19th March 2001

*/

module ordinal.

accumulate arithmetic.
accumulate constructive_logic.

is_otype ordinal ordl [ord_zero] [ord_s, lim].

/*
local ordinaldummy osyn -> o.
ordinaldummy X.
local ordd osyn -> o.
ordd X.
local ordd2 osyn -> o.
ordd2 X.
local ordd3 osyn -> o.
ordd3 X:- printstdout X.
local ordd4 osyn -> o.
ordd4 X:- printstdout X.
local ordd5 osyn -> o.
ordd5 X:- printstdout X.
*/

has_otype ordinal ord_zero ordl.
has_otype ordinal ord_s (arrow [ordl] ordl).
has_otype ordinal lim (arrow [(arrow [nat] ordl)] ordl).

has_otype ordinal ord_plus (arrow [ordl, ordl] ordl).
has_otype ordinal ord_leq (arrow [ordl, ordl] bool).
has_otype ordinal ord_times (arrow [ordl, ordl] ordl).
has_otype ordinal ord_exp (arrow [ordl, ordl] ordl).

injective_left ord_plus _.
injective_right ord_plus _.
injective_left ord_times X:- not (X = ord_zero).
injective_right ord_times X:- not (X = ord_zero).
injective_left ord_exp Y:- not (Y = ord_zero).
injective_right ord_exp _.

definition ordinal ord_plus1
	trueP
	(app ord_plus  [N, ord_zero])
	N.
definition ordinal ord_plus2
	trueP
	(app ord_plus  [X, (app ord_s [Y])])
	(app ord_s [(app ord_plus  [X, Y])]).
definition ordinal  ord_plus3 
	trueP
     	(app ord_plus  [X, (app lim [(abs F nat)])])
     	(app lim [(abs (n\ (app ord_plus  [X, (F n)])) nat)]).

definition arithmetic ord_times1 trueP
   (app ord_times  [_X, ord_zero]) 
   ord_zero.
definition arithmetic ord_times2 trueP
   (app ord_times  [X, (app ord_s [Y])]) 
   (app ord_plus  [(app ord_times  [X, Y]), X]).
definition ordinal ord_times3 
	trueP
    (app ord_times  [X, (app lim [(abs F nat)])])
    (app lim [(abs (z\ (app ord_times  [X, (F z)])) nat)]).

definition arithmetic ord_exp1 trueP
   (app ord_exp  [_X, ord_zero]) 
   (app ord_s [ord_zero]).
definition arithmetic ord_exp2 trueP
   (app ord_exp  [X, (app ord_s [Y])]) 
   (app ord_times  [(app ord_exp  [X, Y]), X]).
definition ordinal ord_exp3 
	trueP
   (app ord_exp  [X, (app lim [(abs F nat)])])
   (app lim [(abs (z\ (app ord_exp  [X, (F z)]))nat)]).

/*
lemma ordinal lim_lim equiv 
	trueP
    (app lim 
        [X, (abs (z\ 
         (app lim 
           [Y, (abs (w\ (app F  [z, w])))])))])
    (app lim 
        [Y, (abs (w\ 
        (app lim 
          [X, (abs (z\ (app F  [z, w])))])))]).
*/

lemma ordinal ord_plus_functional equiv
	trueP
	(app eq  [(app ord_plus  [X, Y]), (app ord_plus  [Z, Y])])
	(app eq  [X, Z]).

lemma ordinal ord_times_functional equiv
	trueP
	(app eq  [(app ord_times  [X, Y]), (app ord_times  [Z, Y])])
	(app eq  [X, Z]).

/*
lemma ordinal lim_suc equiv  
	trueP
      (app lim 
           [(app ord_s X), (abs (y\ y))]) 
      X.
*/
lemma ordinal lim1 equiv
	trueP
    (app eq
          [
          (app lim [(abs F nat)]), 
          (app lim [(abs G nat)])])
    (app forall  [nat,
     (abs (o\ (app eq  [(F o), (G o)])) nat)]).

lemma ordinal lim2 equiv
	trueP
	(app eq  [(app lim [(abs F nat)]), (app ord_s [X])])
	(app forall  [nat, (abs (n\ (app eq  [(F n), (app ord_s [X])])) nat)]).

lemma ordinal lim3 equiv
	trueP
	(app eq  [(app lim [(abs F nat)]), zero])
	(app forall  [nat, (abs (n\ (app eq  [(F n), zero])) nat)]).

axiom arithmetic ord_leq1 equiv trueP
   (app ord_leq [ord_zero, (app ord_s _)])
   trueP.
axiom arithmetic ord_leq2 equiv trueP
   (app ord_leq [(app ord_s _), ord_zero])
   falseP.
axiom arithmetic ord_leq_ss equiv trueP
   (app ord_leq  [(app ord_s [X]), (app ord_s [Y])]) 
   (app ord_leq [X, Y]).

definition ordinal leq3 
	trueP
      (app ord_leq  [(app ord_s [X]), (app lim  [(abs G nat)])])
      (app exists  [ordl,
       (abs (o\ 
          (app ord_leq  [(app ord_s [X]), (G o)])) nat)]).

definition ordinal leq4 
	trueP
      (app ord_leq 
        [(app lim  [X, (abs F nat)]), 
             (app ord_s [Y])])
      (app forall  [ordl,
       (abs (o\ (app ord_leq  [(F o), (app ord_s [Y])])) nat)]).

definition ordinal leq5 
	trueP
        (app ord_leq  
          [(app lim  [(abs F nat)]), 
               (app lim  [(abs G nat)])])
	(app forall  [ordl,
         (abs (o1\ (app exists  [ordl,
            (abs (o2\ (app ord_leq  [(F o1), (G o2)])) nat)])) nat)]).
%
% Induction for ordinals
%
induction_scheme ordinal ordl_ind
    ordl
    (dom (a \ (repl a (app ord_s [a]))))
    (measured ordl Prop)
    ( seqGoal(H >>> (app forall  [ordl, (abs Prop ordl)]) ) Context)
    ( % NB bracket step case goals together
    ( (allGoal ordl z\ (seqGoal (((hyp (otype_of z ordl) nha)::(hyp (Prop z) ind_hyp)::H) >>> 
          (Prop (app ord_s [z]) )) Context)
                    )  **
     (allGoal (arrow [nat] ordl) f\ (seqGoal
       (((hyp (otype_of f (arrow [nat] ordl)) nha)::((hyp (app forall  [nat, 
		(abs (n\ (Prop (app f [n]))) nat)]) ind_hyp)::H))
        >>> (Prop (app lim [(abs (x\ (app f [x])) nat)]))) Context))) **
	(seqGoal( H >>> (Prop ord_zero)) Context)).
%                 :- Id = (abs (Q\ Q) ).

lemma arithmetic ord_s_functional equiv trueP
   (app eq  [(app ord_s [X]), (app ord_s [Y])]) 
   (app eq  [X, Y]).


% Ordinal arithmetic. Step case of inductions contain an extra proof 
% obligation to show that the functions in question respect limits.

% ordinal arithmetic. 
%
top_goal ordinal asspord []
       (app forall  [ordl,
		(abs (z\ (app forall  [ordl,
			(abs (x\ (app forall  [ordl,
	(abs (y\ (app eq  [
		(app ord_plus  [(app ord_plus  [x, y]), z]),
		(app ord_plus  [x, (app ord_plus  [y, z])])])) ordl)])) ordl)])) ordl)]).

% ordinal arithmetic. 
% Suppes
top_goal ordinal plus0ord []
      (app forall  [ordl,
       (abs (o\ 
        (app eq 
          [
          (app ord_plus 
            [ord_zero, o]),
          o])) ordl)]).

% ordinal arithmetic. 
%
top_goal ordinal leqsumord []
      (app forall  [ordl,
		(abs (alpha\ (app forall  [ordl,
	(abs (beta\ (app ord_leq  [alpha, (app ord_plus  [beta, alpha])])) ordl)])) ordl)]).



% ordinal arithmetic. 
%
top_goal ordinal times1ord []
      (app forall  [ordl,
	(abs (alpha\ (app eq  [(app ord_times  [(app ord_s [ord_zero]), alpha]),
		  alpha])) ordl)]).

% ordinal arithmetic. 
%

top_goal ordinal distord []
   (app forall  [ordl,
     (abs (z\ (app forall  [ordl,
       (abs (x\ (app forall  [ordl,
         (abs (y\ (app eq  [
		(app ord_times  [x, (app ord_plus  [y, z])]),
		(app ord_plus  [(app ord_times  [x, y]),
				 (app ord_times  [x, z])])])) ordl)])) ordl)])) ordl)]).

% ordinal arithmetic. 
%
top_goal ordinal assmord []
   (app forall  [ordl,
    (abs (z\ (app forall  [ordl,
     (abs (y\ (app forall  [ordl,
       (abs (x\ (app eq  [
		(app ord_times  [(app ord_times  [x, y]), z]),
		(app ord_times  [x, (app ord_times  [y, z])])])) ordl)])) ordl)])) ordl)]).


% ordinal arithmetic. 
%
top_goal ordinal expplusord []
    (app forall  [ordl,
	(abs (z\ (app forall  [ordl, 
		(abs (x\ (app forall  [ordl,
	(abs (y\ (app eq  [
		(app ord_exp  [x, (app ord_plus  [y, z])]),
		(app ord_times  [(app ord_exp  [x, y]), 
				    (app ord_exp  [x, z])])])) ordl)])) ordl)])) ordl)]).

% ordinal arithmetic. 
%
top_goal ordinal exptimesord []
    (app forall  [ordl, 
	(abs (n\ (app forall  [ordl,
		(abs (m\ (app forall  [ordl,
	(abs (o\ (app eq  [
		(app ord_exp  [o, (app ord_times  [m, n])]),
		(app ord_exp  [(app ord_exp  [o, m]), n])])) ordl)])) ordl)])) ordl)]).

% ordinal arithmetic. 
%
top_goal ordinal leqreflord []
    (app forall  [ordl,
      (abs (n\ (app ord_leq [n, n])) ordl)]).

% ordinal arithmetic. 
%
top_goal ordinal leqsucord []  
     (app forall  [ordl,
       (abs (n\ (app ord_leq  [n, (app ord_s [n])])) ordl)]).

%% Pretty printing

prettify_term lim (str "lim").

lemma ordinal leq_refl equiv
	trueP
	(app ord_leq  [L, L])
	trueP.

lemma ordinal lim1leq equiv
	trueP
    (app ord_leq
          [
          (app lim  [X, (abs F (arrow [nat] ordl))]), 
          (app lim  [X, (abs G (arrow [nat] ordl))])])
    (app forall  [ordl,
     (abs (o\ 
      (app imp  
        [
        (app lt  [o, X]), 
        (app ord_leq  [(F o), (G o)])])) ordl)]).

%% From Hamilton

top_goal ordinal times2ord []
    (app forall  [ordl,
	(abs (alpha\ (app eq  [
		(app ord_times  [alpha, (app ord_s [(app ord_s [ord_zero])])]),
		(app ord_plus  [alpha, alpha])])) ordl)]).
		
top_goal ordinal exp2ord []
   (app forall  [ordl,
	(abs (alpha\ (app eq  [
		(app ord_exp  [alpha, (app ord_s [(app ord_s [ord_zero])])]),
		(app ord_times  [alpha, alpha])])) ordl)]).

top_goal ordinal exp1ord []
  (app forall  [ordl,
	(abs (alpha\ (app eq  [
		(app ord_exp  [(app ord_s [ord_zero]), alpha]),
		(app ord_s [ord_zero])])) ordl)]).

top_goal ordinal leqsumord2 []
	(app forall  [ordl,
	  (abs (alpha\
		(app forall  [ordl,
			(abs (beta\
				(app forall  [ordl,
					(abs (gamma\
	(app imp  [
		(app ord_leq  [beta, gamma]),
		(app ord_leq  [
			(app ord_plus  [alpha, beta]),
			(app ord_plus  [alpha, gamma])])])) ordl)])) ordl)])) ordl)]).

%% Enderton

top_goal ordinal times1leftord []
	(app forall  [ordl,
	  (abs (alpha\
		(app eq  [
			(app ord_times  [(app ord_s [ord_zero]), alpha]),
			alpha])) ordl)]).

top_goal ordinal times0leftord []
	(app forall  [ordl,
	  (abs (alpha\
		(app eq  [
			(app ord_times  [ord_zero, alpha]),
			ord_zero])) ordl)]).

%% Lemma - is this true?

%% Suppes

top_goal ordinal plus1rightord []
	(app forall  [ordl,
		(abs (alpha\
			(app eq  [
				(app ord_plus  [alpha, (app ord_s [ord_zero])]),
				(app ord_s [alpha])])) ordl)]).

top_goal ordinal exp1ord2 []
	(app forall  [ordl,
		(abs (alpha\
			(app eq  [
				(app ord_exp  [alpha, (app ord_s [ord_zero])]),
				alpha])) ordl)]).

benchmark_plan ordinal Meth Query :-
	testloop (%interaction_mode command,
	(% plan_printing on,
	(set_theory_induction_scheme_list ordinal,
	(set_sym_eval_list [idty, lim1, ord_s_functional, mono_fun_1, mono_fun_2, lim2, lim3, leq3, leq4, leq5, ord_leq1, ord_leq2, ord_leq_ss],
	(add_theory_defs_to_sym_eval_list arithmetic,
	(add_theory_defs_to_sym_eval_list ordinal,
	(set_wave_rule_to_sym_eval,
	pds_plan Meth Query))))))).

local ordldum osyn.

has_otype ordinal iter (arrow [(arrow [ordl] ordl), ordl, ordl] ordl).
has_otype ordinal omega ordl.
has_otype ordinal alph ordl.
has_otype ordinal phi (arrow [ordl] ordl).

lemma ordinal iter_lemma equiv
	trueP
	(abs (n\ (app F [(app iter  [F, n, Alpha])])) nat)
	(abs (n\ (app iter  [F, (app ord_s [n]), Alpha])) nat).

lemma ordinal omega_lemma equiv
	trueP
	(app lim  [omega, (abs (n\ (F (app ord_s [n]))) nat)])
	(app lim  [omega, (abs (n\ (F n)) nat)]).

lemma ordinal continuity_lemma equiv
	trueP
	(app phi [(app lim  [(abs (z\ (F z)) nat)])])
	(app lim  [X, (abs (z\ (app phi [(F z)])) nat)]).

top_goal ordinal iterlemma []
	(app forall  [(arrow [ordl] ordl), (abs (f\
		(app forall  [ordl, (abs (n\
			(app forall  [ordl, (abs (alpha\
	(app eq  [
		(app f [(app iter  [f, n, alpha])]),
		(app iter  [f, (app ord_s [n]), alpha])])) ordl)])) ordl)])) (arrow [ordl] ordl))]).

top_goal ordinal fixpoint []
	(app exists  [ordl, (abs (eta\
	(app eq  [(app phi [eta]), eta])) ordl)]).

compound ordinal fixpoint_top_meth (complete_meth
                (repeat_meth
		(orelse_meth triv_eq
                (orelse_meth trivial
                (orelse_meth allFi
                (orelse_meth taut
                (orelse_meth sym_eval
                (orelse_meth existential
                (orelse_meth (repeat_meth generalise)
                         (ind_strat normal_ind)
        )))))))))
	_
        true.

atomic ordinal triv_eq 
	(seqGoal (H >>> (app eq [X, Y])) _)
	(ground_eq X Y)
	true
	trueGoal
	notacticyet.

ground_eq X Y:-
	((X = ordldum); (Y = ordldum)), !, fail.
ground_eq X Y:-
	((not (X = ordldum)), (not (Y = ordldum))),
	X = Y.
ground_eq (app F [X]) (app G [Y]):-
	((not (F = ordldum)), (not (G = ordldum))),
	((not (X = ordldum)), (not (Y = ordldum))),
	ground_eq F G,
	ground_eq X Y.
ground_eq (abs F T) (abs G T):-
	pi x\
		(((not ((F x) = x)), (not ((G x) = x))),
		ground_eq (F x) (G x)).
	
end
