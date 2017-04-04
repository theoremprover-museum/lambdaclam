/*

File: lxtest.mod
Author: Alex Heneveld
Description: predicates to aid with testing
Created: Nov 02

This module lets one conveniently run four types of tests:
commands (predicates), commands which should fail,
queries, and queries which should fail.
One global setup command and one top method can be
specified for two sets of queries.

For example of use, see real_arith in theories/alinteg.

*/

module lxtest.

accumulate lclam.
accumulate constructive_logic.


do_test_battery Label CommandTests CommandAntiTests
  SetupCommand TopMethod NormalQueries AntiQueries :-
  print_line_3 "\nStarting battery of " Label " tests\n",
  print_line_3 "Running " Label " command tests",
  run_tests Label CommandTests ProblemTests, !,
  print_line_3 "Running " Label " command anti-tests",
  run_anti_tests Label CommandAntiTests ProblemAntiTests, !,
  SetupCommand (
     print_line_3 "Running " Label " queries",
     run_queries Label TopMethod NormalQueries ProblemQueries, !,
     print_line_3 "Running " Label " anti-queries",
     run_anti_queries Label TopMethod AntiQueries ProblemAntiQueries, !
  ), !,
  print_summary Label CommandTests CommandAntiTests
    NormalQueries AntiQueries,
  print_results Label ProblemTests ProblemAntiTests ProblemQueries ProblemAntiQueries.

print_summary Label CommandTests CommandAntiTests
    NormalQueries AntiQueries :-
  print "Test battery results for '",
  printterm std_out Label,
  print "': ",
  print_list_count CommandTests "commands, ",
  print_list_count CommandAntiTests "fail-commands, ",
  print_list_count NormalQueries "queries, ",
  print_list_count AntiQueries "fail-queries.\n".
print_list_count List Label :-
  length List Len, !,
  printterm std_out Len, print " ", print Label.

print_results _Label nil nil nil nil :-
  !, print "No violations encountered.\n\n".

print_results _Label ProblemTests ProblemAntiTests ProblemQueries ProblemAntiQueries :-
  !, print "VIOLATIONS!\n",
  print_titled_list "Command-tests which should have passed:" ProblemTests,
  print_titled_list "Command-tests which should have failed:" ProblemAntiTests,
  print_titled_list "Queries which should have passed:" ProblemQueries,
  print_titled_list "Queries which should have failed:" ProblemAntiQueries,
  print "See trace above for more details.\n\n", !, fail.

print_titled_list _Label nil :- !.
print_titled_list Label List :- !,
  print_line_1 Label,
  print_prefixed_list "  " List.

print_prefixed_list Prefix (H::T) :-
  print Prefix, print_item H, print "\n",
  print_prefixed_list Prefix T.
print_prefixed_list _Prefix nil.

print_item A :-
  term_to_string A AS,
  BS is substring AS 0 1,
  BS = """",
  print A, !.
print_item A :-
  printterm std_out A.

print_line_1 I1 :-
  print_item I1, print "\n".
print_line_2 I1 I2 :-
  print_item I1, print_item I2, print "\n".
print_line_3 I1 I2 I3 :-
  print_item I1, print_item I2, print_item I3, print "\n".
print_line_4 I1 I2 I3 I4 :-
  print_item I1, print_item I2, print_item I3, 
  print_item I4, print "\n".
print_line_5 I1 I2 I3 I4 I5 :-
  print_item I1, print_item I2, print_item I3, 
  print_item I4, print_item I5, print "\n".

run_tests Label (T1::TT) PT :-
  print_line_4 "Running " Label " command-test " T1,
  T1, !,
  print_line_5 "Command-test " Label " " T1 " succeeded (as desired)\n", !,
  run_tests Label TT PT.
run_tests Label (T1::TT) (T1::PT) :- !,
  print_line_5 "LXTEST VIOLATION: Command-test " Label " " T1 " FAILED\n", !,
  run_tests Label TT PT.
run_tests Label nil nil :-
  print_line_3 "Finished " Label " command-tests\n".

run_anti_tests Label (T1::TT) (T1::PT) :-
  print_line_4 "Running " Label " command anti-test " T1,
  T1, !,
  print_line_5 "LXTEST VIOLATION: Command anti-test " Label " " T1 " SUCCEEDED (it shouldn't have)\n", !,
  run_anti_tests Label TT PT.
run_anti_tests Label (T1::TT) PT :- !,
  print_line_5 "Command anti-test " Label " " T1 " failed (as desired)\n", !,
  run_anti_tests Label TT PT.
run_anti_tests Label nil nil :-
  print_line_3 "Finished " Label " command anti-tests\n".

run_queries Label Meth (T1::TT) PT :-
  print_line_4 "Running " Label " plan-query " T1,
  pds_plan Meth T1, !,
  print_line_5 "Plan-query " Label " " T1 " succeeded (as desired)\n", !,
  run_queries Label Meth TT PT.
run_queries Label Meth (T1::TT) (T1::PT) :- !,
  print_line_5 "LXTEST VIOLATION: plan-query " Label " " T1 " FAILED\n", !,
  run_queries Label Meth TT PT.
run_queries Label _Meth nil nil :-
  print_line_3 "Finished " Label " queries\n".

run_anti_queries Label Meth (T1::TT) (T1::PT) :-
  print_line_4 "Running " Label " plan anti-query " T1,
  pds_plan Meth T1, !,
  print_line_5 "LXTEST VIOLATION: plan anti-query " Label " " T1 " SUCCEEDED (it shouldn't have)\n", !,
  run_anti_queries Label Meth TT PT.
run_anti_queries Label Meth (T1::TT) PT :- !,
  print_line_5 "Plan anti-query " Label " " T1 " failed (as desired)\n", !,
  run_anti_queries Label Meth TT PT.
run_anti_queries Label _Meth nil nil :-
  print_line_3 "Finished " Label " anti-queries\n".

nop.

with_nop NextCommand :-
  NextCommand.

test_lxtest :-
  do_test_battery "sample" (nop::flop::nil) (nop::flop::nil) with_nop id_meth nil nil.


end
