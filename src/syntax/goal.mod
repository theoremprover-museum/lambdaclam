/*

File: goal.mod
Author: Louise Dennis / James Brotherston
Description: Support for goals, sequents and queries in lclam
Last Modifed: 13th August 2002

*/

module goal.
accumulate lclam_utils.

reduce_goal trueGoal trueGoal.
reduce_goal (trueGoal ** X) Y :- reduce_goal X Y, !.
reduce_goal (X ** trueGoal) Y :- reduce_goal X Y, !.
reduce_goal (X ** Y) Z :- reduce_goal X XX, reduce_goal Y YY, 
                          reduce_goal (XX ** YY) Z.
reduce_goal (_X vv trueGoal) trueGoal.   % backtracking?
reduce_goal (trueGoal vv _Y) trueGoal.   % also ??
reduce_goal (allGoal _ G) H :-
   pi i\ (reduce_goal (G i) H).
reduce_goal (existsGoal _ G) H :-
   pi i\ (reduce_goal (G i) H).         % if goal does not depend

list2goal nil trueGoal.
list2goal (X::nil) X.
list2goal (X::(Y::T)) (X ** G):-
	list2goal (Y::T) G.

compound_goal trueGoal.
compound_goal falseGoal.
compound_goal (allGoal _ _).
compound_goal (existsGoal _ _).
compound_goal (_ ** _).

top_goal_c A B C D []:-
	   top_goal A B C D.

update_gb_context (allGoal Type G) (allGoal Type G1) P:-
		  pi x\ (update_gb_context (G x) (G1 x) P).
update_gb_context (G1 ** G2) (NewG1 ** NewG2) P:-
		  update_gb_context G1 NewG1 (1::P),
		  update_gb_context G2 NewG2 (2::P).
update_gb_context (seqGoal (Hyps >>> Goal) Context) 
		  (seqGoal (Hyps >>> Goal) ((unsure X OUTINFO)::NewRest)) P:-
	  not (P = []),
	memb_and_rest (unsure X RRINFO) Context Rest,
	mappred RRINFO (RINFO\ OutINFO\ 
                        sigma Rule\ sigma Info\ sigma Used\ sigma Used2\ (
		RINFO = (rrstatus Rule Info Pointer Used),
		new_rr_point Pointer Info,
		append Pointer P NewPointer,
		((not (Used = 0), Used2 = Used); true),
		OutINFO = (rrstatus Rule Info NewPointer Used2))) OUTINFO,
	update_gb_context (seqGoal (Hyps >>> Goal) Rest) (seqGoal (Hyps >>> Goal) NewRest) P.
update_gb_context G G P.
	

local new_rr_point (list int) -> good_bad_tree -> o.

new_rr_point [] (gbnode L R).
new_rr_point (1::T) (gbnode L R):-
	     new_rr_point T L.
new_rr_point (2::T) (gbnode L R):-
	     new_rr_point T R.


fetch_rr_point [] N N.
fetch_rr_point (1::T) (gbnode L R) Out:-
	     fetch_rr_point T L Out.
fetch_rr_point (2::T) (gbnode L R) Out:-
	     fetch_rr_point T R Out.

end
