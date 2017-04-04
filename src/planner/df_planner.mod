 /*

File: df_planner.mod
Author: Louise Dennis
Description: Depth First Planner.
Last Modified: 17th November 2000

*/

module df_planner.

accumulate df_support.

local build_plan plan -> plan -> plan -> o.

%%%%%%%%%%%%%%%%%%%
%% DF ALGORITHM - NO CRITICS
%%%%%%%%%%%%%%%%%%%

df_plan (pstate Agenda (and_node G A S Method M P NL T Path)) AP (pstate _ PlanOut):-
	df_planner Method G _ PlanOut.

df_planner Method  (allGoal Type AtoGoal) (allGoal Type BtoGoal) (forall_node _ Type (X\ [AtoPlan X])) :- !,
	pi z\ (df_planner Method (AtoGoal z) (BtoGoal z) (AtoPlan z)).
df_planner Method 
    (existsGoal Type AtoGoal) GG  (exists_node _ Type (X\ [AtoPlan X])):- !,
           (df_planner Method (AtoGoal Wit) GG (AtoPlan Wit)).
df_planner id_meth In In (and_node In _ open_status nomethodyet id_meth nil nil notacticyet [id_meth]):- !.
df_planner (orelse_meth M1 M2) G G' Plan:- !,
	(df_planner M1 G G' Plan;
	 df_planner M2 G G' Plan).
df_planner (cond_meth C M1 M2) G G' Plan:- !,
	(C G, !, df_planner M1 G G' Plan;
	 df_planner M2 G G' Plan).
df_planner (try_meth M) In Out Plan:- !,
	df_planner (orelse_meth M id_meth) In Out Plan.
df_planner (then_meth M1 M2) In Out Plan:- !,
	df_planner M1 In Mid Plan1,
	map_expand (df_planner M2) Mid Out Plan2,
	build_plan Plan1 Plan2 Plan.
df_planner (then_meths M1 M2) In Out Plan:- !,
	df_planner M1 In Mid Plan1, 
	df_planner M2 Mid Out Plan2,
	build_plan Plan1 Plan2 Plan.	
df_planner (pair_meth M2 M3) (I1 ** I2) (O1 ** O2) Plan:- !,
	df_planner M2 I1 O1 P1,
	df_planner M3 I2 O2 P2,
	build_plan _ (and_node _ _ partial_status nomethodyet nomethodyet nil [P1, P2] notacticyet nil) Plan.
df_planner (repeat_meth M) In Out Plan:- !,
	keep_variables_free M M1,
	df_planner (then_meth M (orelse_meth (repeat_meth M1) id_meth))
	 In Out Plan.
df_planner (map_meth M) In Out Plan:- !,
	map_expand (df_planner M) In Out Plan.
df_planner (complete_meth M) In Out Plan:- !,
	df_planner M In Mid Plan, 
	reduce_goal Mid trueGoal.
df_planner (cut_meth M) In Out Plan:- !,
	df_planner M In Out Plan, !.
df_planner triv_meth trueGoal trueGoal (and_node trueGoal _ complete_status nomethodyet nomethodyet nil nil notacticyet nil):- !.
df_planner Method In Out Plan:-
	pprint_goal In,
	pprint_string "Attempting...",
	pprint_name Method,
	expand_compound_method Method Methodical _Preconditions,
	pprint_name Method,
	pprint_string "succeeded\n",
	df_planner Methodical In Out Plan.
df_planner Method In Out (and_node In _ open_status nomethodyet Method Pre nil notacticyet [Method]):-
	apply_method_to_goal (addmeth _ _) Method In Out Pre,
	pprint_name Method,
	pprint_string "succeeded\n".
	
build_plan (and_node G A S M C P _ T Pa) (and_node _ _ _ nomethodyet nomethodyet _ CL _ _) (and_node G A S M C P CL T Pa):- !.
build_plan  (and_node G A S M C P _ T Pa) Plan (and_node G A S M C P [Plan] T Pa):- !.
build_plan (forall_node Ad Type AtoPlan) Plan (forall_node Ad Type BtoPlan):-
	pi z\ (mappred (AtoPlan z) (X\ Y\ build_plan X Plan Y) (BtoPlan z)), !.
end