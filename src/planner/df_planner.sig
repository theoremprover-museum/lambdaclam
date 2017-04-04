/*

File: df_planner.sig
Author: Louise Dennis
Description: Depth First Planner.
Last Modified: 21st November 2000.

*/

sig df_planner.

accum_sig df_support.

type df_plan plan_state -> (action -> plan_state -> plan_state -> o) -> plan_state -> o.

type df_planner meth -> goal -> goal -> plan -> o.

end