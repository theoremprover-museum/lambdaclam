/*

File: real_arith.sig
Author: Alex Heneveld
Description: define real nums, arithmetic
Created: Oct 02 (based on work in Jan 00)

*/

sig real_arith.

accum_sig lxtest.
accum_sig rewriting.
	  
type real_arith theory.

% -------------------- HELPERS ------------------------ 

type	is_permut  (list osyn) -> (list osyn) -> o.
type	remove	   T -> (list T) -> (list T) -> o.
type	remove_all osyn -> (list osyn) -> (list osyn) -> o.
type	list_contains (list A) -> A -> o.
type	unpack osyn -> (list osyn) -> (list osyn) -> o.
type	prettify_list  thing -> (list osyn) -> thing -> o.
type	append_lists (list A) -> (list A) -> (list A) -> o.
type 	const_expr  osyn -> o.
type	has_subterm osyn -> o.

type not_equal osyn -> osyn -> o.

% ------------------ BASIC NUMS ------------------------ 

type	reals osyn.
type	reals_list (list osyn) -> o.

type 	r_zero osyn.
type    r_one osyn.

type	undefined osyn.
type	nonzero osyn -> o.
type	notzero osyn -> o.
type	r_equal osyn -> osyn -> o.
type	r_is_integer osyn -> o.

% --------------------- PLUS -------------------------- 

type    plus osyn.
% makes an osyn representing the sum of the first terms in the second
% (smart, in the sense that if it's 0 or 1 obj it writes 1 or X, not times...)
type	make_plus_obj	(list osyn) -> osyn -> o.

% plus(a) = a
type    plus_single rewrite_rule. 
% a+0 = a
type    plus_id rewrite_rule.
% a+(b+c)+d = a+b+c+d
type	plus_plus rewrite_rule.

%type	prettify_int int -> string -> o.
%type	prettify_integers int -> (list osyn) -> int -> (list osyn) -> o.


% ------------------- TIMES -------------------------- 

type    times osyn.
% makes an osyn representing the product of the first terms in the second
% (smart, in the sense that if it's 0 or 1 obj it writes 1 or X, not times...)
type	make_times_obj	(list osyn) -> osyn -> o.

% A*1*B = A*B
type    times_id rewrite_rule.
% A*0 = 0
type    times_zero rewrite_rule.
% times(A) = A
type	times_single rewrite_rule.
% A*(B*C)*D = A*B*C*D
type	times_times rewrite_rule.

% X*N*Y*N2 = N*N2*X*Y (move const terms to front)
type	times_const rewrite_rule.
% helper preds for above
type	move_const_expr_to_front (list osyn) -> (list osyn) -> o.
type	move_const_expr_to_front_2 (list osyn) -> (list osyn) -> o.

% a*(b+c)*d = a*b*d + a*c*d
type	dist_times_plus rewrite_rule.
% helper pred for above
type	factor_through_at  (list osyn) -> (list osyn) -> int -> (list osyn) -> o.

% a*b + a*c = a*(b+c)
type collect_plus_times rewrite_rule.
type collect_obvious_factors rewrite_rule.

% splits up factors from the first term into consts (2nd) and vars (3rd)
type separate_const_terms osyn -> (list osyn) -> (list osyn) -> o.

% ------------------ NEG / MINUS -------------------------- 

type    neg osyn.
type	neg_one osyn.
% boolean determinining if two things are additive inverses
type	known_additive_inverses osyn -> osyn -> o.

% -x = (-1)*x
type	neg_x		rewrite_rule.
% a+(c*d)+b+(-1*d*c) = a+b
type    plus_additive_inverses	rewrite_rule.
% (-1)*(-1)=1
type	times_neg_neg	rewrite_rule.
% -1*(a+b+c) = ((-1*a)+(-1*b)+(-1*c))
type	neg_sum		rewrite_rule.

type    minus osyn.
type    minus_to_plus_neg rewrite_rule.


% -------------------- DIV_BY -------------------------- 

type	div_by osyn.
type	div_zero_by rewrite_rule.
type	div_by_one rewrite_rule.
type	div_by_neg_one	rewrite_rule.
type	div_by_neg_one_factor	rewrite_rule.
type	times_div_by	rewrite_rule.
type	div_div_by	rewrite_rule.
type	div_by_div_by	rewrite_rule.
type	plus_div_by	rewrite_rule.
type	div_x_by_x_1	rewrite_rule.
type	div_x_by_x_2	rewrite_rule.
type	div_x_by_x_3	rewrite_rule.
type	div_x_by_x_4	rewrite_rule.


% --------------------- MISC ------------------------- 

type	beta_redux	rewrite_rule.

type fn_idty osyn.
type fn_indep osyn.
type def_fn_idty rewrite_rule.
type def_fn_indep rewrite_rule.


% ----------------- ALGEBRA METHODS ------------------------ 

type rearrange_set_equal_zero meth.


% ----------------- SUMMARY METHODS ------------------------ 

type    arith_top_meth meth.

type	real_arith_methods (meth -> meth).
type	arith_general_methods meth.
type    tauts_meth meth.
type    collect_terms (meth -> meth).
type	expand_then_collect (meth -> meth).
type	combine_fracs (meth -> meth).

type  general_rewrites  osyn.
type  expand_rewrites  osyn. 
type  collect_rewrites  osyn.
type  combine_fracs_rewrites  osyn.

type clear_rewrites_set osyn -> o -> o.
type with_rewrites_set osyn -> (list rewrite_rule) -> o -> o.
type with_theory_rewrites_set theory -> osyn -> o -> o.

type rewrites_set theory -> osyn -> (list rewrite_rule) -> o.
type rewrites_set_nil theory -> osyn -> (list rewrite_rule) -> o.

type apply_rewrites osyn -> meth. 
type try_apply_rewrites osyn -> meth. 

type apply_rewrites_record osyn -> (list rewrite_rule) -> osyn -> osyn -> meth.
type try_apply_rewrites_record osyn -> (list rewrite_rule) -> osyn -> osyn -> meth.
type do_apply_rewrites_1 (list rewrite_rule) -> (list rewrite_rule) -> (list osyn) -> osyn -> osyn -> o.
type do_apply_rewrites_2 (list rewrite_rule) -> (list rewrite_rule) -> (list osyn) -> osyn -> osyn -> o.

 
% defined in rewriting.sig...doesn't work just to define it here.
%type rewrite_with_rules (list rewrite_rule) -> rewrite_rule ->
%                         osyn -> osyn -> osyn -> o.


% -------------------- QUERIES ------------------------ 

type    test_plus_1	query.
type    test_plus_2	query.
type	test_redux_1	query.
type	test_redux_2	query.
type 	test_times_1	query.
type 	test_times_2	query.
type 	test_times_3	query.
type 	test_times_plus_1	query.
type 	test_dist_1	query.
type	test_plus_neg_1	query.
type 	test_minus_1	query.
type	test_div_by_1	query.

type	test_fail_plus	query.
type	test_fail_dist	query.

type test_dist_const_1 query.
type test_dist_const_2 query.
type test_dist_const_3 query.

type test_add_fracs_1 query.

type test_dist_times_plus_1 query.
type do_test_dist_times_plus_1 o.
type do_test_dist_times_plus_fail_1 o.

type do_test_remove_all_1 o.
type do_test_remove_all_fail_1 o.

type test_collect_1 query.
type do_test_collect_1 o.
type test_fail_collect_1 query.
type do_test_fail_collect_1 o.

% --------------- SUMMARY / SETUP / TEST ------------------------ 

type do_real_arith_tests o.

type setup_real_arith o.
type with_setup_real_arith o -> o.
type clear_arith_rewrites o.
type with_clear_arith_rewrites o -> o.

type real_arith_tests osyn.
type real_arith_anti_tests osyn.
type real_arith_queries osyn.
type real_arith_anti_queries osyn.

end
