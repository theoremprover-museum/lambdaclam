/*

File: real_fns.sig
Author: Alex Heneveld
Description: fns for reals
Created: Oct 02 (based on work in Jan 00)

*/

sig real_fns.

accum_sig real_arith.
	  
type real_fns theory.

% -------------------- GENERAL ------------------

type known_inverse_fns osyn -> osyn -> o.
type get_inverse_fn osyn -> osyn -> o.
type cancel_inverse_fns rewrite_rule.


% ---------------------- POW ---------------------
type pow osyn.
type pow_zero_zero rewrite_rule.
type pow_zero_x rewrite_rule.
type pow_x_zero rewrite_rule.
type pow_x_one rewrite_rule.
type pow_one_x rewrite_rule.
type pow_pow_a_x_y rewrite_rule.
type times_pow_x_a_x_b rewrite_rule.
type power_expression osyn -> osyn -> osyn -> o.
type pow_times_a_b_to_x rewrite_rule.
type apply_pow osyn -> (list osyn) -> (list osyn) -> o.

type r_e osyn.
type exp osyn.
type log osyn.

% a^p = e^((log a)*p)
type pow_as_exp rewrite_rule.
type exp_zero rewrite_rule.
type pow_as_exp_nonconst rewrite_rule.
% e^(..*log b*..) = b^(..*..)
type exp_log_as_pow rewrite_rule.

% ----------------------- METHODS --------------------
type fns_top_meth meth.

% ------------------------ TESTS -----------------------

type test_pow_1 query.
type test_pow_one_x query.
type test_pow_two_x query.
type test_fail_pow_zero_x query.
type test_fail_pow_x_zero query.
type test_fail_pow_1 query.
type test_log_exp_1 query.
type test_collect_pow_x_1 query.

% -------------------- SUMMARY / SETUP / TEST -----------------

type setup_real_fns o.
type with_setup_real_fns o -> o.

type do_real_fns_tests o.

type real_fns_tests osyn.
type real_fns_anti_tests osyn.
type real_fns_queries osyn.
type real_fns_anti_queries osyn.
