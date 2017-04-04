/*

File: df_support.sig
Author: Louise Dennis
Description: Support for Depth First Planner
Last Modified: 10th November 2000

*/

sig df_support.

accum_sig plan_support.

type map_expand (goal -> goal -> plan -> o) -> goal -> goal -> plan -> o.

end