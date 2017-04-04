/*

File: real_fns.mod
Author: Alex Heneveld
Description: fns for the reals
Created: Oct 02 (based on work in Jan 00)

*/

module real_fns.

accumulate real_arith.

% ------------------ GENERAL --------------------

known_inverse_fns log exp.

definition real_fns cancel_inverse_fns trueP
  (app A (app B X))
  X :- 
    get_inverse_fn A B.

get_inverse_fn In Out :- known_inverse_fns In Out, !.
get_inverse_fn In Out :- known_inverse_fns Out In, !.

%
% -------------------- POW ----------------------- 
%

has_otype real_fns pow ((tuple_type [reals, reals]) arrow reals).

prettify_special (app pow (tuple [A, B]))
  (blo 1 [str "(", AA, str ")^(", BB, str ")"]):-
  !, prettify_term A AA, prettify_term B BB.

r_is_integer (app pow A) :- r_is_integer A.

% pow(0^0) error
definition real_fns pow_zero_zero trueP
  (app pow (tuple [r_zero, r_zero]))
  undefined.


% 0^x = 0
definition real_fns pow_zero_x trueP
  (app pow (tuple [r_zero, X]))
  r_zero :- notzero X.   %@todo ought to be nonzero
 
% x^0 = 1
definition real_fns pow_x_zero trueP
  (app pow (tuple [X, r_zero]))
  r_one :- nonzero X.  %@todo ought to be nonzero

% 1^X = 1
definition real_fns pow_one_x trueP
  (app pow (tuple [r_one, X]))
  r_one.

% x^1 = x
definition real_fns pow_x_one trueP
  (app pow (tuple [X, r_one]))
  X.

% (a^x)^y = a^(x*y)
definition real_fns pow_pow_a_x_y trueP
  (app pow (tuple [(app pow (tuple [A, X])), Y]))
  (app pow (tuple [A, (app times (tuple [X, Y]))])).

% x^a * x^b = x^(a+b)   (including x = x^1)
definition real_fns times_pow_x_a_x_b trueP
  (app times (tuple FACTORS))
  (app times (tuple NEW_FACTORS)) :-
  power_expression EXPR1 X A,
  remove EXPR1 FACTORS FACTORS_1,
  power_expression EXPR2 X B,
  remove EXPR2 FACTORS_1 FACTORS_2,
  append_lists FACTORS_2 ( (app pow (tuple [X, (app plus 
     (tuple [A, B]))])) :: nil) NEW_FACTORS.

power_expression (app pow (tuple [A, X])) A X.
power_expression A A r_one.

% x^a/x^b
% x/x^b
% x^a/x

% (ab)^x = a^x*b^x
definition real_fns pow_times_a_b_to_x trueP
  (app pow (tuple [(app times (tuple FACTORS)), X]))
  (app times (tuple NEW_FACTORS)) :-
    apply_pow X FACTORS NEW_FACTORS.
    
apply_pow X (nil) (nil).
apply_pow X (FH :: FT) ((app pow (tuple [FH, X])) :: NFT) :-
  apply_pow X FT NFT.


%
% -------------------- E EXP LOG ------------------------ 
%

has_otype real_fns r_e reals.
has_otype real_fns exp (reals arrow reals).
has_otype real_fns log (reals arrow reals).

prettify_special (app log A)
  (blo 1 [str "log(", AA, str ")"]):-
  !, prettify_term A AA.

prettify_special (app exp A)
  (blo 1 [str "exp(", AA, str ")"]):-
  !, prettify_term A AA.

definition real_fns exp_zero trueP
  (app exp r_zero)
  r_one.

% e^a*e^b = e^(a+b)
% better done as methodical which
% writes as pow(..) then simplifies then writes back as exp(..)

% a^p = e^((log a)*p)
definition real_fns pow_as_exp trueP
  (app pow (tuple [A, P]))
  (app exp (app times (tuple [(app log A), P]))).

% a^p = e^((log a)*p)
definition real_fns pow_as_exp_nonconst trueP
  (app pow (tuple [A, P]))
  (app exp (app times (tuple [(app log A), P]))) :-
  not ( const_expr P ).

% e^(..*log b*..) = b^(..*..)
definition real_fns exp_log_as_pow trueP
  (app exp P)
  (app pow (tuple [B, P2])) :-
    make_times_obj F P,
    remove (app log B) F F2,
    make_times_obj F2 P2.

%
% ------------------- METHODS ----------------------
%

compound real_fns fns_top_meth (complete_meth
    (real_arith_methods arith_general_methods)
  )
  _
  true.

% no special methods for fns...
% (it's all done with rewrites)

%
% -------------------- TESTS ------------------------ 
%

% (XY)^2 * Y^(-2) = X^2
top_goal real_fns test_pow_1 []
	  (app forall (tuple [reals, (abs X\ 
  	    (app forall (tuple [reals, (abs Y\ 
              (app eq (tuple [
                 (app times (tuple [
 	          (app pow (tuple [
 	           (app times (tuple [X, Y])),
                   (app plus (tuple [r_one, r_one]))])),
                  (app pow (tuple [Y, (app neg (app plus (tuple
	           [r_one, r_one])))]))
		  ])),
		 (app times (tuple [X, X]))
	 ])))])))])).

top_goal real_fns test_pow_one_x []
	  (app forall (tuple [reals, (abs X\ 
              (app eq (tuple [
                 (app pow (tuple [r_one, X])),
                 r_one])) )])).

% 2^X = 2*2^(X-1)
top_goal real_fns test_pow_two_x []
	  (app forall (tuple [reals, (abs X\ 
              (app eq (tuple [
                 (app pow (tuple [(app plus (tuple [r_one, r_one])), X])),
                 (app times (tuple [(app plus (tuple [r_one, r_one])),
                   (app pow (tuple [(app plus (tuple [r_one, r_one])),
                     (app minus (tuple [X, r_one]))])) ]))               
     ])) )])).

% should fail if X=0...  but right now it is actually "proven" by our system
top_goal real_fns test_fail_pow_zero_x []
	  (app forall (tuple [reals, (abs X\ 
              (app eq (tuple [
                 (app pow (tuple [r_zero, X])),
                 r_zero])) )])).

top_goal real_fns test_fail_pow_x_zero []
	  (app forall (tuple [reals, (abs X\ 
              (app eq (tuple [
                 (app pow (tuple [X, r_zero])),
                 r_one])) )])).

% (XY)^4 * Y^(-2) = (XY)^2
top_goal real_fns test_fail_pow_1 []
	  (app forall (tuple [reals, (abs X\ 
  	    (app forall (tuple [reals, (abs Y\ 
              (app eq (tuple [
                 (app times (tuple [
 	          (app pow (tuple [
 	           (app times (tuple [X, Y])),
                   (app plus (tuple [r_one, r_one, r_one, r_one]))])),
                  (app pow (tuple [Y, (app neg (app plus (tuple
	           [r_one, r_one])))]))
		  ])),
		 (app pow (tuple [
                   (app times (tuple [X, Y])),
                   (app plus (tuple [r_one, r_one]))
	 ]))])))])))])).

% log(exp(2))=2
top_goal real_fns test_log_exp_1 []
  (app eq (tuple [
    (app log (app exp (app plus (tuple [r_one, r_one])))), 
    (app plus (tuple [r_one, r_one])) ])).

% 3x^2 /2 + -x^2 /2 = x^2
top_goal real_arith test_collect_pow_x_1 []
  (app forall (tuple [reals, (abs X\ (app eq (tuple [
    app plus (tuple [
      app div_by (tuple [
        app times (tuple [
          app plus (tuple [r_one, r_one, r_one]), 
          app pow (tuple [X, app plus (tuple [r_one, r_one])]) ]),
        app plus (tuple [r_one, r_one]) ]),
      app div_by (tuple [
        app times (tuple [neg_one, 
          app pow (tuple [X, app plus (tuple [r_one, r_one])])]), 
        app plus (tuple [r_one, r_one])]) ]), 
    app pow (tuple [X, app plus (tuple [r_one, r_one])])
  ])))])).


%
% ------------------ SUMMARY / SETUP / TEST  ------------------------ 
%
	
do_real_fns_tests :-
  test_set real_fns_tests T,
  test_set real_fns_anti_tests AT,
  test_set real_fns_queries Q,
  test_set real_fns_anti_queries AQ,
  do_test_battery "real_fns" T AT
    with_setup_real_fns fns_top_meth Q AQ.

test_set real_fns_tests nil.
test_set real_fns_anti_tests nil.

test_set real_fns_queries [
  test_pow_one_x,
  test_pow_1,
  test_pow_two_x,
  test_fail_pow_zero_x,
  test_fail_pow_x_zero,
  test_log_exp_1,
  test_collect_pow_x_1
].

test_set real_fns_anti_queries [
  test_fail_pow_1
].

rewrites_set real_fns general_rewrites [
  cancel_inverse_fns,
  pow_zero_zero, pow_zero_x, pow_x_zero, pow_x_one, pow_one_x,
  pow_pow_a_x_y, times_pow_x_a_x_b,
  pow_times_a_b_to_x,
  times_pow_x_a_x_b,
  exp_zero
].

rewrites_set real_fns expand_rewrites [
  pow_as_exp_nonconst
].

setup_real_fns :- with_setup_real_fns lclam.
with_setup_real_fns Loop :-
  with_setup_real_arith (
    (with_theory_rewrites_set real_fns general_rewrites
    (with_theory_rewrites_set real_fns expand_rewrites
    (Loop)))).

%
% write pow as exp as sep method.
%

end
