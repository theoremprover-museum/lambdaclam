/*

File: test_set_gen.mod
Author: Louise Dennis
Description:  Generates sets of ground terms for a given type.
Last Modified: 12th December 2000

*/

module test_set_gen.

type cut_base osyn -> (list osyn) -> (list osyn) -> o.
type cut_step int -> osyn -> (list osyn) -> (list osyn) -> o.

%% define a cut on a function type as a constant
cut N (arrow [_] Type) Out:-
	((N > 0, N1 is (N - 1)); N1 = 0),
	cut N1 Type Terms,
	mapfun Terms (Term\ (abs (X\ Term) _)) Out.
cut N (arrow (H1::(H2::T)) Type) Out:-
	((N > 0, N1 is (N - 1)); N1 = 0),
	cut N1 (arrow (H2::T) Type) Terms,
	mapfun Terms (Term\ (abs (X\ Term) _)) Out.
	
cut 0 Type Cut:-
	is_otype _ Type BaseConstructors _,
	cut_base Type BaseConstructors Cut, 
	!.
cut N Type Cut:-
	NewN is (N - 1),
	NewN >= 0,
	cut NewN Type CutpN,
	is_otype _ Type _ StepConstructors,
	((cut NewN Type CutpN) =>
	cut_step N Type StepConstructors Cut), !.


cut_base Type nil nil:-!.
cut_base Type (H::T) (H::TOut):-
	has_otype _ H Type,
	cut_base Type T TOut, !.
cut_base Type (H::T) Out:-
	has_otype _ H (arrow TypeList Type),
	mappred TypeList (X\ Cut\ (cut 0 X Cut)) Cuts,
	findall (Term\ 
		(mappred Cuts (X\ Y\ (memb Y X)) Term)) TermList,
	findall (Term\ (sigma Arg\
		(memb Arg TermList,
		 Term = (app H Arg))))
		Terms,
	cut_base Type T TOut,
	append Terms TOut Out, !.


	
cut_step _ Type nil nil:-!.
cut_step N Type (H::T) Out:-
	has_otype _ H (arrow TypeList Type),
	(NewN is (N - 1)),
	mappred TypeList (X\ Cut\ (
		((headvar_osyn X, X = nat); (not (headvar_osyn X))),
		cut NewN X Cut
		)) Cuts,
	findall (Term\ 
		(mappred Cuts (X\ Y\ (memb Y X)) Term)) TermList,
	findall (Term\ (sigma Arg\
		(memb Arg TermList,
		 Term = (app H Arg))))
		Terms,
	cut_step N Type T TOut,
	append Terms TOut Out, !.

end
