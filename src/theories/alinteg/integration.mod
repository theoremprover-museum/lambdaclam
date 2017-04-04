/*

File: real_integ.mod
Author: Alex Heneveld
Description: tying them all together...
Created: Nov 02 (based on work in Jan 00)

*/

module integration.

accumulate real_integ.

do_all_tests :-
  do_real_arith_tests,
  do_real_fns_tests,
%  do_real_trig_tests,
  do_real_deriv_tests,
  do_real_integ_tests,
  print "\nAll tests for all alinteg modules succeeded.\n\n".

local x osyn.
prettify_special x (blo 1 [str "x"]).

evaluate What Input Result :-
  with_clear_arith_rewrites (
  with_setup_real_integ (
  pds_plan (alinteg_evaluate_top_meth Result)
       (evaluation_query What Input)
  )), !,
  print "\n",
  print_eval_result What Input Result,
  print "\n".

local print_eval_result osyn -> osyn -> osyn -> o.

print_eval_result What (abs X\ (Input X)) (abs X\ (Result X)) :-
    print "The ", printterm std_out What, print " of ",
    pprint_term (Input x),
    print "             is ",
    pprint_term (Result x), !.

print_eval_result What Input Result :-
    print "The ", printterm std_out What, print " of ",
    pprint_term Input,
    print "             is ",
    pprint_term Result, !.


evaluate What Input _Result :-
  print "\n\nCould not evaluate ",
  printterm std_out What,
  print " ",
  pprint_term Input,
  !,
  fail.

top_goal integration (evaluation_query integral Input) []
  (app evaluate_integ (app integ Input)).

top_goal integration (evaluation_query derivative Input) []
  (app evaluate_deriv (app deriv Input)).

compound integration (alinteg_evaluate_top_meth Result)
  (complete_meth
    (real_arith_methods (integ_general_methods Result))
  ) _ true.

help :-
  print "Choose one of the following samples:\n",
  print "  sample 1.    test whether  integral(3x-x) = x^2+C\n",
  print "  sample 2.    evaluate the deriv of x^x\n",
  print "  sample 3.    try to evaluate the integ of x^x (will fail)\n",
  print "\nOr something like:\n",
  print "   evaluate integral (abs X\\ (app exp X)) Result.\n",
  print "   evaluate derivative (abs X\\ (app log (app plus (tuple [r_one, app sin X])))) _.\n",
  print "or 'help_real_queries' to see a list of relevant queries available.\n",
  print "\n".

sample 1 :-
  print "\n\nSample:  test whether integral(3x-x) = x^2+C\n\n",
  with_setup_real_integ
  (pds_plan integ_top_meth test_integ_3x_minus_x_eq_x_sqr),
  !,
  print "\n\nScroll up to see the answer and how it was gotten.\n\n".

sample 2 :-
  print "\n\nSample:  eval the deriv of x^x\n",
  with_setup_real_deriv
  (pds_plan deriv_top_meth test_deriv_pow_x_x),
  !,
  print "\n\nScroll up to see the answer and how it was gotten.\n\n".

sample 3 :-
  print "\n\nSample:  try to evaluate the integ of x^x (will fail)\n",
  with_setup_real_integ
  (pds_plan integ_top_meth test_integ_pow_x_x),
  !,
  print "\n\n(you probably won't see this, as the plan will fail!)\n\n".

help_real_queries :-
  print "\n\nThe following pre-defined queries are available:\n\n",
  list_real_queries,
  print "\nEnter 'pds_plan integ_top_meth QueryName.' to attempt to prove a query.\n",
  print "(You must 'setup_real_integ.' before doing any planning.)\n".

local list_real_queries o.
list_real_queries :-
  alinteg_module Theory,
  top_goal Theory Query _A _Value,
  print "  ",
  printstdout Query,
  fail.
list_real_queries.

alinteg_module integration.
alinteg_module real_arith.
alinteg_module real_fns.
alinteg_module real_trig.
alinteg_module real_deriv.
alinteg_module real_integ.

end
