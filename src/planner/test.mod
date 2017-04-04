/*

File: test.mod
Author: Louise Dennis
Description:  Testings lclam still works!!
Last Modified: 7th March 2001

*/

module test.

accumulate objlists.
accumulate constructive_logic.

/*
local testdummy o -> o.
testdummy X.

local testdummy2 o -> o.
testdummy2 _.

local testdummy3 o -> o -> o.
testdummy3 X _:-
	   printstdout X.
*/


benchmark_plan test Meth Query :-
%	print "Executing benchmark plan\n",
	testloop (set_theory_induction_scheme_list arithmetic,
	(add_theory_to_induction_scheme_list objlists,
	(set_sym_eval_list [idty, s_functional, cons_functional, leq1, leq2, leq_ss, assAnd1, prop3, prop4, prop5, prop6],
	(add_theory_defs_to_sym_eval_list arithmetic,
	(add_theory_defs_to_sym_eval_list objlists,
	(set_wave_rule_to_sym_eval,
	pds_plan Meth Query)))))).


/*
testpds:-
	testloop (
	pprint_string "Checking Basic Planning Mechanism\n",
	(plan_this pds_planner taut taut2 depth_first_plan P,
	(pprint_string "Checking Symbolic Evaluation\n",
	(set_sym_eval_list [idty],
	(plan_this pds_planner (then_meth (then_meth sym_eval trivial) triv_meth) eqzero depth_first_plan P,
	(pprint_string "Checking Rippling Out\n",
	(set_sym_eval_list [plus1, plus2, idty],
	(set_wave_rule_list [plus2, s_functional],
	(set_induction_scheme_list [nat_struct],
	(plan_this pds_planner (induction_top normal_ind) assp depth_first_plan P,
	(pprint_string "Checking Generalisation\n",
	(set_sym_eval_list [exp1, exp2, times1, times2, plus1, plus2, idty],
	(set_wave_rule_list [exp1, times2, plus2, s_functional],
	(set_induction_scheme_list [nat_struct],
	(plan_this pds_planner (induction_top normal_ind) assm depth_first_plan P, 
	(pprint_string "Checking lists\n",
	(set_sym_eval_list [oapp1, oapp2, cons_functional, idty],
	(set_wave_rule_list [oapp1, oapp2, cons_functional],
	(set_induction_scheme_list [list_struct],
	(plan_this pds_planner (induction_top normal_ind) assapp depth_first_plan P
	))))))))))))))))))))
	))))) 
	.
*/

end
