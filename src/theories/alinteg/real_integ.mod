/*

File: real_integ.mod
Author: Alex Heneveld
Description: integration
Created: Nov 02 (based on work in Jan 00)

*/

module real_integ.

accumulate real_deriv.

%
% ----------------------- INTEGRAL -----------------------
%

has_otype real_integ integ ((reals arrow reals) arrow (reals arrow reals)).

prettify_special (app integ F)
  (blo 1 [str "Intgrl[", FF, str "]"]) :- !, prettify_term F FF.

% I(n) = n.X
known_deriv (abs X\ (app times (tuple [N, X]))) (abs X\ N).

% I(x^n) = x^(n+1)/(n+1)
% @todo  n+1 computation may give zero.
known_deriv
   (abs X\ (app div_by (tuple [
     (app pow (tuple [X, (app plus (tuple [N, r_one]))])), (app plus (tuple [N, r_one])) ])))
   (abs X\ (app pow (tuple [X, N]))) :- 
   not ( N = neg_one ).

known_deriv
  A (abs X\ X) :- known_deriv A (abs X\ (app pow (tuple [X, r_one]))).

% integ of first term is second

% I(A+B) = I A + I B
rule_integ integ_plus 
  (abs X\ (app plus (tuple (HA X::HT X)))) 
  (abs X\ (app plus (tuple [
     (app (app integ (abs Y\ HA Y)) X),
     (app (app integ (abs Y\ (app plus (tuple (HT Y))))) X)
  ]))).

% I(k.B) = k.I(B)
rule_integ integ_times_const 
  (abs X\ (app times (tuple (HA::HT X)))) 
  (abs X\ 
     (app times (tuple [HA, (app (app integ (abs Y\ (app times (tuple (HT Y))))) X) ]))
  ).

%
% ----------------------- "plus C" REDUCTION ---------------
%

% @todo

%
% ---------------- SOLVE SYNTAX / METHODS ----------------------
%

has_otype real_integ evaluate_integ ((reals arrow reals) arrow bool).

compound real_integ (integ_general_methods Result)
  (then_meth (deriv_general_methods Result)
  (try_meth 
    (repeat_meth
      (then_meth evaluate_integ_query
      (orelse_meth (evaluate_integ_done Result)
        (repeat_meth
          (then_meth
            (orelse_meth (repeat_meth (evaluate_integ_known))
                (evaluate_integ_expand))
            (deriv_general_methods Result)
     )))))
   ) )
   _
   true.

% succeeds if there is a integ in the expression, or a req to evaluate_integ
atomic real_integ (evaluate_integ_query)
        ( seqGoal (H >>> G))
	(subterm_of G integ _Pos1 ; subterm_of G evaluate_integ _Pos2)
        true 
        (seqGoal (H >>> G))
        notacticyet :- !.

% replaces any (app evaluate_integ X) where X does not contain a integ.
atomic real_integ (evaluate_integ_done Result)
        ( seqGoal (H >>> G))
	(subterm_of G (app evaluate_integ Result) Pos,
	 not(subterm_of Result (app integ _X2) _Pos2), 
         print "EVALUATE_INTEG GOT ANSWER: ",
         printstdout Result,
         replace_at G trueP G1 Pos
        )
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

% replaces any solveable integ
atomic real_integ (evaluate_integ_known)
        ( seqGoal (H >>> G))
	(subterm_of G (app integ X) Pos,
	 known_deriv Y X,
         replace_at G Y G1 Pos
        )
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

% replaces any solveable integ
atomic real_integ (evaluate_integ_expand)
        ( seqGoal (H >>> G))
	(subterm_of G (app integ X) Pos,
	 rule_integ Rule X Y,
         list_contains [integ_times_const, integ_plus] Rule,
         replace_at G Y G1 Pos
        )
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

compound real_integ integ_top_meth (complete_meth
    (real_arith_methods (integ_general_methods _Result))
  ) _ true.


%
% ---------------------- TESTS ----------------------
%

top_goal real_integ test_eval_integ_x_1 []
  (app evaluate_integ (app integ (abs X\ X))).

top_goal real_integ test_eval_integ_3x_minus_x []
  (app evaluate_integ (app integ (abs X\ 
    (app minus (tuple [
       (app times (tuple [X, 
         (app plus (tuple [r_one, r_one, r_one]))])),
       X]))
  ))).

top_goal real_integ test_integ_3x_minus_x_eq_x_sqr []
 (app forall (tuple [reals, (abs U\ 
  (app eq (tuple [(app (app integ (abs X\ 
    (app minus (tuple [
       (app times (tuple [X, 
         (app plus (tuple [r_one, r_one, r_one]))])),
       X]))
  )) U),
  (app (abs X\ (app times (tuple [X, X]))) U) ])) )])).

top_goal real_integ test_integ_pow_x_x []
  (app evaluate_integ (app integ (abs X\ 
    (app pow (tuple [X, X])) ))).

top_goal real_integ test_integ_one_eq_one_fail []
  (app forall (tuple [reals, (abs U\ 
    (app eq (tuple [(app (app integ (abs X\ r_one)) U), r_one]))
  )])).


%
% --------------- SUMMARY / SETUP / TEST ------------------------ 
%

do_real_integ_tests :-
  test_set real_integ_tests T,
  test_set real_integ_anti_tests AT,
  test_set real_integ_queries Q,
  test_set real_integ_anti_queries AQ,
  do_test_battery "real_integ" T AT
    with_setup_real_integ integ_top_meth Q AQ.

setup_real_integ :- with_setup_real_integ (testloop nop).
with_setup_real_integ Loop :- 
  with_setup_real_deriv
% no special rewrites here
  (Loop).

% list of commands which must pass
test_set real_integ_tests (
  nil).

% list of commands which MUST NOT PASS
test_set real_integ_anti_tests (
  nil).

% list of tests which must pass in normal operation
test_set real_integ_queries [
     test_eval_integ_x_1,
     test_eval_integ_3x_minus_x,
%    test_integ_pow_x_x query,  %for now we can't do this
     test_integ_3x_minus_x_eq_x_sqr
  ].

% list of tests which MUST NOT PASS in normal operation
test_set real_integ_anti_queries [
    test_integ_one_eq_one_fail
  ].

end
