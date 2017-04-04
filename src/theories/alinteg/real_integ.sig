/*

File: real_integ.mod
Author: Alex Heneveld
Description: differentiation
Created: Nov 02 (based on work in Jan 00)

*/

sig real_integ.

accum_sig real_deriv.

type real_integ theory.

% ------------------------- D ------------------------

type integ osyn.
type integral osyn.

% takes two fn args (abs X\ ...), the 2d is the Intgral of the 1st
type rule_integ rewrite_rule -> osyn -> osyn -> o.
type integ_times_const rewrite_rule.
type integ_plus rewrite_rule.

% app to quantity to signal we want to know if the integ can be evaluated
type evaluate_integ osyn.


% ---------------- SOLVE SYNTAX / METHODS ----------------------

% extension of real_arith general_methods to do integatives
type integ_general_methods osyn -> meth.
type evaluate_integ_query meth.
type evaluate_integ_done osyn -> meth.
type evaluate_integ_known meth.
type evaluate_integ_expand meth.

type integ_top_meth meth.

type test_eval_integ_x_1 query.
type test_eval_integ_3x_minus_x query.
type test_integ_3x_minus_x_eq_x_sqr query.
type test_integ_pow_x_x query.
type test_integ_one_eq_one_fail query.

% ---------------------- SUMMARY / SETUP -------------------

type do_real_integ_tests o.

type setup_real_integ o.
type with_setup_real_integ o -> o.

type real_integ_tests osyn.
type real_integ_anti_tests osyn.
type real_integ_queries osyn.
type real_integ_anti_queries osyn.
