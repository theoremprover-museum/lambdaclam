/*

File: conjecture_tester.sig
Author: Louise Dennis
Description: A conjecture tester (currently based around cuts) - see BBNOTE 1223.
Last Modified: 11th December 2000

*/

sig conjecture_tester.

accum_sig test_set_gen, logic_eq_constants.

kind truth_label type.

%% Label truth shows whether any
%% subgoals are found to be true, false or undecided.
type label_truth int -> int -> int -> truth_label.

type conjecture_tester theory.

type formula_tester (list int) -> meth -> truth_label -> meth.
type generate_ground_instances (list int) -> meth.
type pick_label (truth_label) -> meth.
type evaluate meth.
type type_constructors rewrite_rule.
type contains_meta_var_goal goal -> o.

%% from rewrite and elsewhere

type rewrite_with_rules_eval (list rewrite_rule) -> osyn -> osyn -> osyn -> o.
type trivial_condition osyn -> list osyn -> o.
type  rewrite_using  osyn -> osyn -> osyn -> mkey -> int -> osyn -> o.
type beta_reduce (list osyn) -> osyn -> osyn -> o.

type beta_reduction rewrite_rule.
type imp1 rewrite_rule.
type imp2 rewrite_rule.
type imp3 rewrite_rule.
type and1 rewrite_rule.
type and2 rewrite_rule.
type and3 rewrite_rule.
type and4 rewrite_rule.
type or1 rewrite_rule.
type or2 rewrite_rule.
type or3 rewrite_rule.
type or4 rewrite_rule.
type neg1 rewrite_rule.
type neg2 rewrite_rule.
type iff1 rewrite_rule.

type banned (list rewrite_rule) -> context.
type partition_rw (list A) -> (list A) -> (list A) -> (list A) -> o.

end
