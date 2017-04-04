/*

File: generalise.mod
Author: Louise Dennis
Description: The generalise method.
Last Modifed: 7th March 2001

*/

module generalise.

accumulate coerce_meta_vars.

local   gener           goal -> osyn -> goal -> o.
                                     % subterm appropriate for generalisation,
                                     % giving new sequent
local   quantify_gener  goal -> goal -> o.
local   compound_gen    osyn -> o.


compound gen generalisation_compound
	(cond_meth contains_any_meta_var_goal fail_meth 
		(then_meth (repeat_meth generalise)
			(cond_meth already_false id_meth (formula_tester [0,2] evaluate (label_truth _ 0 _)))))
	Address
	(check_path Address).

local check_path (list int) -> o.
check_path [].
check_path (H::T):-
	   get_method T nomethodyet, !,
	   check_path T.
check_path (H::T):-
	   get_method T (generate_ground_instances _), !, fail.
check_path (H::T):-
	   get_method T generalise, !, fail.
check_path (H::T):-
 	   get_method T M, !.
check_path (H::T) :-
	   check_path T.


local already_false goal -> o.
already_false (seqGoal (H >>> G) Context):-
	member (unsure _ _) Context.

atomic gen generalise
        InG
        ( gener InG T NewGoal )
        true 
	NewGoal 
	notacticyet.


gener (seqGoal (H >>> (app eq [A, B])) Context) T   
      (seqGoal (H >>> (app forall [Type, (abs (v\ (app eq [(NewA v), (NewB v)])) Type)])) Context) :-
                A = (NewA T),
                compound_gen T,
		not (constant T _),
                B = (NewB T), 
               	not ( NewA = (x\ _AA)),
                not ( NewB = (x\ _BB)),
		pi x\ (not (subterm_of (app eq [(NewA x), (NewB x)]) T _)),
                env_otype_inst_types T H Type,
		%% What does this line accomplish ?
		%% It instantiates the type of T,
                env_otype_inst_types (NewA T) ((hyp (otype_of T Type) nha)::H) _.

gener (seqGoal (H >>> G) Context) T   
      (seqGoal (H >>> (app forall [Type, (abs (v\ (NewG v)) Type)])) Context) :-
		not (G = (app eq [_, _])),
		subterm_of G (app F [LHS, RHS]) _,
	        lemma _ _ _ trueP (app transitive [F]) trueP,
                LHS = (NewA T),
                compound_gen T,
		not (constant T _),
                RHS = (NewB T), 
		G = (NewG T),
               	not ( NewA = (x\ _AA)),
                not ( NewB = (x\ _BB)),
		pi x\ (not (subterm_of (NewG x) T _)),
                env_otype_inst_types T H Type,
		%% What does this line accomplish ?
		%% It instantiates the type of T,
                env_otype_inst_types (NewG T) ((hyp (otype_of T Type) nha)::H) _.

% infer object type for generalisation

% infer object type for generalisation
gener (seqGoal (H >>> (app forall [Ty, (abs Body Ty)])) Context) (abs T _) New :-
	( pi X\ (gener (seqGoal (((hyp (otype_of X Ty) nha) :: H) >>> (Body X)) Context) (T X)
                       (seqGoal (((hyp (otype_of X Ty) nha) :: H) >>> (NewBody X)) Context)
                )
        ),
      quantify_gener (seqGoal (H >>> (app forall [Ty, (abs NewBody Ty)]))Context ) New.

% mode: quantify_gener + -
%
% If generalisation results in one of the goal's universally quantified 
% variables being deleted from the goal, then omit the corresponding
% quantifier, i.e. introduce the quantifier and thin the newly introduced
% constant away.
% '
quantify_gener (seqGoal (H >>> (app forall [Ty, (abs (x\ NewBody) Ty)])) Context)
               (seqGoal (H >>> NewBody) Context).

quantify_gener (seqGoal (H >>> (app forall [Ty, (abs (x\ (NewBody x)) Ty)])) Context)
               (seqGoal (H >>> (app forall [Ty, (abs (x\ (NewBody x)) Ty)])) Context).

compound_gen (app _ _).

contains_any_meta_var_goal (seqGoal (H >>> G) _):-
	contains_meta_var_term G.
contains_any_meta_var_goal (seqGoal (H >>> G) _):-
	for_one H (X\ contains_meta_var_term X) _.



end
