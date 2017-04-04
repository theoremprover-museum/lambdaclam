/*

File: goal.sig
Author: Louise Dennis / James Brotherston
Description: Support for goals, sequents and queries in lclam
Last Modifed: 13th August 2002

*/

sig goal.

accum_sig basic_types.

type user_query string -> query.

type trueGoal goal.
type falseGoal goal.
type **       goal -> goal -> goal.     % conjunction
type vv       goal -> goal -> goal.     % disjunction
type allGoal   osyn -> (A -> goal) -> goal.
type existsGoal osyn -> (A -> goal) -> goal.     

type   >>>     (list osyn) -> osyn -> osyn.
type   seqGoal osyn -> (list context) -> goal.  

infix ** 200.
infix vv 200.
infix >>> 100.

%% Support Predicate
type reduce_goal  goal -> goal -> o.

type top_goal theory -> query -> (list osyn) -> osyn -> o.
type top_goal_c theory -> query -> (list osyn) -> osyn -> (list context) -> o.

type list2goal (list goal) -> goal -> o.

type compound_goal goal -> o.

kind rewrite_info type.
kind good_bad_tree type.
kind rr_status type.

type good rr_status.
type bad rr_status.
type unknown rr_status.

type unsure osyn -> (list rewrite_info) -> context.
type rrstatus rewrite_rule -> good_bad_tree -> (list int) -> int -> rewrite_info.
type gbleaf rr_status -> good_bad_tree.
type gbnode  good_bad_tree -> good_bad_tree -> good_bad_tree.

type update_gb_context goal -> goal -> (list int) -> o.
type fetch_rr_point (list int) -> good_bad_tree -> good_bad_tree -> o.


end
