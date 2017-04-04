/*

File: real_deriv.mod
Author: Alex Heneveld
Description: differentiation
Created: Nov 02 (based on work in Jan 00)

*/

module real_deriv.

accumulate real_trig.

%
% ------------------------- D ------------------------
%

has_otype real_deriv deriv ((reals arrow reals) arrow (reals arrow reals)).

prettify_special (app deriv F)
  (blo 1 [str "D[", FF, str "]"]) :- !, prettify_term F FF.

known_deriv (abs X\ X) (abs X\ r_one).
known_deriv (abs X\ Z) (abs X\ r_zero).
%known_deriv (abs X\ (app pow (tuple [X, app plus (tuple [r_one, r_one])])))
%  (abs X\ (app times (tuple [app plus (tuple [r_one, r_one]), X]))).
known_deriv (abs X\ (app pow (tuple [X, N]))) 
  (abs X\ (app times (tuple [N, (app pow (tuple [X, (app minus (tuple [N, r_one]))]))]))).
known_deriv (abs X\ (app exp X)) (abs X\ (app exp X)).
known_deriv (abs X\ (app log X)) (abs X\ (app div_by (tuple [r_one, X]))).
known_deriv (abs X\ (app div_by (tuple [N, X])))
  (abs X\ (app div_by (tuple [app neg N, 
    (app pow (tuple [X, app plus (tuple [r_one, r_one])])) ]))).

% written explicitly so we can eval d(A/B) w/o needing a 
% decomposition step
%   A/B = A * 1/B
% (though maybe a decomp step would be better ?)
known_deriv (abs X\ (app div_by (tuple [X, N]))) 
  (abs X\ (app div_by (tuple [r_one, N]))).

known_deriv (abs X\ (app sin X)) (abs X\ (app cos X)).
known_deriv (abs X\ (app cos X)) (abs X\ (app neg (app sin X))).

% d(A+B) = dA + dB
rule_deriv (abs X\ (app plus (tuple (HA X::HT X)))) 
  (abs X\ (app plus (tuple [
     (app (app deriv (abs Y\ HA Y)) X),
     (app (app deriv (abs Y\ (app plus (tuple (HT Y))))) X)
  ]))).

% d(A.B) = A.d(B) + d(A).B
rule_deriv (abs X\ (app times (tuple (HA X::HT X)))) 
  (abs X\ (app plus (tuple [
     (app times (tuple [HA X, (app (app deriv (abs Y\ (app times (tuple (HT Y))))) X) ])),
     (app times (tuple ((app (app deriv (abs Y\ HA Y)) X)::HT X)))
  ]))).

% d(f(g(X))) = D[f](g(x)) * D[g(x)]
% st G not identity, G not a tuple
rule_deriv (abs X\ (app F (G X)))
  (abs X\ (app times (tuple [
    (app (app deriv (abs U\ (app F U))) (G X)), 
    (app (app deriv (abs U\ G U)) X) ]))) :-
  not ( pi u\ (G u = u) ),
  not ( pi u\ (G u = (tuple (_GG u)))).
% above, for generic 2-arg fns (eg div_by and pow)
% using partials (okay maybe this one isn't a great model of human subjects ;)
rule_deriv (abs X\ (app F (tuple [G X, H X])))
  (abs X\ 
    (app plus (tuple [
      (app times (tuple [
       DF1 (H X) (G X),
       (app (app deriv (abs G)) X) ])),
      (app times (tuple [
       DF2 (G X) (H X),
       (app (app deriv (abs H)) X) ]))
  ]))) :-
    ((pi X\ ((G X) = _GC)), DF1 = (X1\ X2\ r_zero), ! ;
     pi N1\ 
       (known_deriv (abs X\ (app F (tuple [X, N1]))) (abs X\ ((DF1 N1) X)))),
    ((pi X\ ((H X) = _HC)), DF2 = (X1\ X2\ r_zero), ! ;
     pi N2\ 
       (known_deriv (abs X\ (app F (tuple [N2, X]))) (abs X\ ((DF2 N2) X)))).

% derivative of inv fn
% require d of inv to be known,
% otherwise can make inf loop
rule_deriv (abs X\ (app FI (G X)))
  (abs X\ (app div_by (tuple [
    (app (app deriv (abs U\ G U)) X),
    DF (app FI X)
  ]))) :- get_inverse_fn F FI,
    known_deriv (abs X\ (app F X)) (abs DF).


%
% ---------------- SOLVE SYNTAX / METHODS ----------------------
%

has_otype real_deriv evaluate_deriv ((reals arrow reals) arrow bool).

compound real_deriv (deriv_general_methods Result)
  (then_meth arith_general_methods
  (try_meth 
    (repeat_meth
      (then_meth evaluate_deriv_query
      (orelse_meth (evaluate_deriv_done Result)
        (repeat_meth
          (then_meth
            (orelse_meth (repeat_meth (evaluate_deriv_known))
                (evaluate_deriv_expand))
            arith_general_methods
     )))))
   ) )
   _
   true.

% succeeds if there is a deriv in the expression, or a req to evaluate_deriv
atomic real_deriv (evaluate_deriv_query)
        ( seqGoal (H >>> G))
	(subterm_of G deriv _Pos1 ; subterm_of G evaluate_deriv _Pos2)
        true 
        (seqGoal (H >>> G))
        notacticyet :- !.

% replaces any (app evaluate_deriv X) where X does not contain a deriv.
atomic real_deriv (evaluate_deriv_done Result)
        ( seqGoal (H >>> G))
	(subterm_of G (app evaluate_deriv Result) Pos,
	 not(subterm_of Result (app deriv _X2) _Pos2), 
         print "EVALUATE_DERIV GOT ANSWER: ",
         printstdout Result,
         replace_at G trueP G1 Pos
        )
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

% replaces any solveable deriv
atomic real_deriv (evaluate_deriv_known)
        ( seqGoal (H >>> G))
	(subterm_of G (app deriv X) Pos,
	 known_deriv X Y,
         replace_at G Y G1 Pos
        )
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

% replaces any solveable deriv
atomic real_deriv (evaluate_deriv_expand)
        ( seqGoal (H >>> G))
	(subterm_of G (app deriv X) Pos,
	 rule_deriv X Y,
         replace_at G Y G1 Pos
        )
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

compound real_deriv deriv_top_meth (complete_meth
    (real_arith_methods (deriv_general_methods _Result))
  ) _ true.






top_goal real_deriv test_eval_deriv_kx []
  (app evaluate_deriv (app deriv (abs X\ 
    (app minus (tuple [
       (app times (tuple [X, 
         (app plus (tuple [r_one, r_one, r_one]))])),
       X]))
  ))).

top_goal real_deriv test_eq_deriv_kx_k []
  (app eq (tuple [(app deriv (abs X\ 
    (app minus (tuple [
       (app times (tuple [X, 
         (app plus (tuple [r_one, r_one, r_one]))])),
       X]))
  )),
  (abs X\ (app plus (tuple [r_one, r_one]))) ])).

top_goal real_deriv test_eval_deriv_log []
  (app evaluate_deriv (app deriv (abs X\ (app log X)))).

top_goal real_deriv test_deriv_exp_log []
  (app eq (tuple [(app deriv (abs X\ 
      (app exp (app log X))  
    )), (abs U\ r_one)])).

top_goal real_deriv test_deriv_pow_x_x []
  (app evaluate_deriv (app deriv (abs X\ 
    (app pow (tuple [X, X])) ))).

top_goal real_deriv test_deriv_pow_x_x_fail []
  (app eq (tuple [ (app deriv (abs X\ 
    (app pow (tuple [X, X])) )), (abs X\ X) ] )).


top_goal real_deriv test_fail_deriv_x_x []
  (app forall (tuple [reals, (abs U\ 
    (app eq (tuple [(app (app deriv (abs X\ X)) U), U]))
  )])).

do_command_test simple_antideriv_test :-
  known_deriv (abs U) (abs X\ r_one),
  pi x\ (U x = x).

do_command_test simple_antideriv_fail_test :-
  known_deriv (abs U) (abs X\ r_one),
  pi x\ (U x = r_one).

top_goal real_deriv test_deriv_sin_sqr []
  (app evaluate_deriv (app deriv (abs X\ 
    (app pow (tuple [(app sin X), (app plus (tuple [r_one, r_one]))]))
  ))).

top_goal real_deriv test_deriv_sin_sin_eq_deriv_sin_sqr []
  (app forall (tuple [reals, (abs U\ (app eq (tuple [
    (app (app deriv (abs X\ 
       (app pow (tuple [(app sin X), (app plus (tuple [r_one, r_one]))]))
      )) U),
    (app (app deriv (abs X\ 
       (app times (tuple [(app sin X), (app sin X)]))
      )) U)
  ])))])).

% would really like to unlearn d[log] for this,
% but we cheat a bit
do_command_test deriv_log_from_inv_test :-
   (( (known_deriv (abs X\ (app exp X)) (abs X\ (app log X)) :- !) )
%      (known_deriv r_zero r_zero :- !, fail ) ) 
=> 
      (pds_plan deriv_top_meth test_eval_deriv_log) ).

%
% --------------- SUMMARY / SETUP / TEST ------------------------ 
%

do_real_deriv_tests :-
  real_deriv_tests T,
  real_deriv_anti_tests AT,
  real_deriv_queries Q,
  real_deriv_anti_queries AQ,
  do_test_battery "real_deriv" T AT
    with_setup_real_deriv deriv_top_meth Q AQ.

setup_real_deriv :- with_setup_real_deriv (testloop nop).
with_setup_real_deriv Loop :- 
  with_setup_real_fns
% no special rewrites here
  (Loop).

% list of commands which must pass
real_deriv_tests (
%    (do_command_test simple_antideriv_test) ::
  nil).

% list of commands which MUST NOT PASS
real_deriv_anti_tests (
%    (do_command_test simple_antideriv_fail_test) ::
  nil).

% list of tests which must pass in normal operation
real_deriv_queries [
    test_eval_deriv_kx, test_eq_deriv_kx_k,
    test_eval_deriv_log,
    test_deriv_exp_log, test_deriv_pow_x_x,
    test_deriv_sin_sqr, test_deriv_sin_sin_eq_deriv_sin_sqr
  ].

% list of tests which MUST NOT PASS in normal operation
real_deriv_anti_queries [
    test_fail_deriv_x_x
%, test_deriv_pow_x_x_fail    %commented out cuz it takes a LONG time
%                              (or mebbe never finishes)
  ].




% cut_meth would really speed things up...hacks lots of places
% so that methods always succeed, w/o using try_meth (to avoid
% backtracking over id_meth...

end
