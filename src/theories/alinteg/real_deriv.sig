/*

File: real_deriv.mod
Author: Alex Heneveld
Description: differentiation
Created: Nov 02 (based on work in Jan 00)

*/

sig real_deriv.

%accum_sig real_trig.
accum_sig real_trig.

type real_deriv theory.

% ------------------------- D ------------------------

type deriv osyn.
type derivative osyn.

% takes two fn args (abs X\ ...), the 2d is the D of the 1st
type known_deriv osyn -> osyn -> o.
type rule_deriv osyn -> osyn -> o.

% app to quantity to signal we want to know if the deriv can be evaluated
type evaluate_deriv osyn.


% ---------------- SOLVE SYNTAX / METHODS ----------------------

% extension of real_arith general_methods to do derivatives
type deriv_general_methods osyn -> meth.
type evaluate_deriv_query meth.
type evaluate_deriv_done osyn -> meth.
type evaluate_deriv_known meth.
type evaluate_deriv_expand meth.

type deriv_top_meth meth.

type test_eval_deriv_kx query.
type test_eq_deriv_kx_k query.
type test_eq_deriv_const_zero query.
type test_eval_deriv_log query.
type test_deriv_exp_log query.
type test_deriv_pow_x_x query.
type test_deriv_pow_x_x_fail query.
type test_fail_deriv_x_x query.

type do_command_test osyn -> o.

type simple_antideriv_test osyn.
type simple_antideriv_fail_test osyn.

type test_deriv_sin_sqr query.
type test_deriv_sin_sin_eq_deriv_sin_sqr query.

type deriv_log_from_inv_test osyn.

% ---------------------- SUMMARY / SETUP -------------------
type do_real_deriv_tests o.

type setup_real_deriv o.
type with_setup_real_deriv o -> o.

type real_deriv_tests (list o) -> o.
type real_deriv_anti_tests (list o) -> o.
type real_deriv_queries (list query) -> o.
type real_deriv_anti_queries (list query) -> o.

