/*
 * File: coerce_meta_vars
 * Author: Louise Dennis
 * meta-variable coercion onto a project of arguments
 * in order to try and eagerly instantiate meta-vars
 */

module coerce_meta_vars.

accumulate conjecture_tester.

local projection osyn -> int -> o.
local no_projection (osyn -> osyn) -> int -> o.
local coerce_vars_pred osyn -> o.

compound coerce_meta_vars coerce_vars
	(then_meth try_projection
		 (formula_tester [0, 3] evaluate (label_truth _ 0 0)))
	_
	true.

atomic coerce_meta_vars try_projection
	(seqGoal (H >>> G) Context)
	(coerce_vars_pred G,
	 env_otype_inst_types G H _,
%%	 printstdout "b",
%%	 printstdout Context,
	 for_each Context (X\ sigma Conc\ sigma Lemma\
	  ((X = (newgen Conc Lemma),
		 beta_reduce H Lemma D,
		 not (redundant_forall_eq D Conc)
		 );
	  not (X = (newgen _ _))))
	 )
	true
	 (seqGoal (H >>> G) Context)
	notacticyet.

local redundant_forall_eq osyn -> osyn -> o.
redundant_forall_eq X X.
redundant_forall_eq (app forall [_, (abs (X\ (F X)) _)])
		    (app forall [_, (abs (X\ (G X)) _)]):-
		    pi x\ (redundant_forall_eq (F x) (G x)).
redundant_forall_eq (app forall [_, (abs (X\ (F X)) _)]) Term:-
		    pi x\ (redundant_forall_eq (F x) Term).

coerce_vars_pred (app F L):-
	headvar_osyn F,
	length L N,
	projection F N,
	for_each L coerce_vars_pred.
coerce_vars_pred (app F L):-
	not (headvar_osyn F),
	coerce_vars_pred F,
	for_each L coerce_vars_pred.
coerce_vars_pred (abs F _):-
	pi x\ (coerce_vars_pred (F x)).
coerce_vars_pred X:-
	headvar_osyn X, !,
	fail.
coerce_vars_pred X:- !,
	(not (X = (app _ _))),
	(not (X = (abs _ _))).



projection (abs (X\ X) _) 1.
projection (abs (X\ F1) _) N:-
	N > 1,
	N1 is (N - 1),
	projection F1 N1.
projection (abs (X\ (F1 X)) _) N:-
	N > 1,
	N1 is (N - 1),
	no_projection F1 N1.

no_projection (X\ (abs (Y\ X) _)) 1.
no_projection (X\ (abs (Y\ (Y1 X)) _)) N:-
	N > 1,
	N1 is (N - 1),
	no_projection (X\ (Y1 X)) N1.

end
