module ftl.

accumulate basic_tacs.
accumulate examples.

%
% ------------------- top is the top command (not surprisingly)
%

% check a tactic or a proof against a formula
check_ Proof Phi :-
  (repeat_tac (app_list!_tac (
    pre2 tax::pre tlnot::pre trnot::pre tlimp::pre trimp::pre tlall::pre trall::pre tlbox::pre trbox::
    pre tliff::pre triff::pre tland::pre trand::pre tlor::pre tror::pre tlsome::pre trsome::pre tldia::pre trdia::
    trefleq::pre tsubeq::pre2 tsubeql::pre2 tsubeqr::close_tac::pre tlbef::pre trbef::
    tser::trefl::ttrans::twdir::tsdir::twconn::pret tsconn::tatom::nil)))
 (Proof proves ([] --> [Phi])) true_goal.

% interactive tp
top Phi :-
  tinter Tactic (Proof proves ([] --> [Phi])) OutGoal, print_ "\n",
  (
    ( OutGoal = true_goal, trim Tactic Tactic',
      print_ "----> Proof found. Formula\n\t", write_ Phi, print_ "\n",
      print_ "----> is proved by tactic\n\t", write_ Tactic', print_ "\n",
      print_ "----> which generates proof\n\t", write_ Proof, print_ "\n\n",
      print_ "Check tactic? ", read Ans, (Ans = y, check_ Proof Phi; true) );
    ( print_ "----> Stopped. Tactic so far:\n", write_ Tactic, print_ "\n" )
  ).

% lousy trick to avoid logical vars in leaves.
trim (then_tac (try_tac Tac) Tac') Tac :- not(not(Tac' = id_tac)), not(not(Tac' = fail_tac)).
trim (pair_tac Tac1' Tac2') (pair_tac Tac3' Tac4') :- trim Tac1' Tac3', trim Tac2' Tac4'.
trim (then_tac (try_tac Tac) Tac') (then_tac (try_tac Tac) Tac1') :- trim Tac' Tac1'.

tinter (then_tac (try_tac Tac) Tac') (P proves (Gamma --> Delta)) NewGoal :-
  print_   "\n\n----- Premises:\n",    wlist_ Gamma 1,
  print_     "\n----- Conclusions:\n", wlist_ Delta 1,
  print_ "\n\n***** Tactic? ", read Tac,
  tproc (then_tac (try_tac Tac) Tac') (P proves (Gamma --> Delta)) NewGoal.

tproc (then_tac (try_tac tback) _) _ _ :- !, print_ "--> Backtracking.", fail. % backtrack
tproc (then_tac (try_tac Tac) (pair_tac Tac1' (pair_tac Tac2'
          (pair_tac Tac3' (pair_tac Tac4' Tac5'))))) OldGoal NewGoal :-        % open five branches
  not(Tac = then_tac _ _),
  Tac OldGoal (and_goal MidGoal1 (and_goal MidGoal2
              (and_goal MidGoal3 (and_goal MidGoal4 MidGoal5)))),
  map_tac (tinter Tac1') MidGoal1 NewGoal1,
  map_tac (tinter Tac2') MidGoal2 NewGoal2,
  map_tac (tinter Tac3') MidGoal3 NewGoal3,
  map_tac (tinter Tac4') MidGoal4 NewGoal4,
  map_tac (tinter Tac5') MidGoal5 NewGoal5,
  goalr_tac (and_goal NewGoal4 NewGoal5) NewGoal45,
  goalr_tac (and_goal NewGoal3 NewGoal45) NewGoal34,
  goalr_tac (and_goal NewGoal2 NewGoal34) NewGoal23,
  goalr_tac (and_goal NewGoal1 NewGoal23) NewGoal.
tproc (then_tac (try_tac Tac) (pair_tac Tac1' (pair_tac Tac2'
                              (pair_tac Tac3' Tac4')))) OldGoal NewGoal :-    % open four branches
  not(Tac = then_tac _ _),
  Tac OldGoal (and_goal MidGoal1 (and_goal MidGoal2
              (and_goal MidGoal3 MidGoal4))),
  map_tac (tinter Tac1') MidGoal1 NewGoal1,
  map_tac (tinter Tac2') MidGoal2 NewGoal2,
  map_tac (tinter Tac3') MidGoal3 NewGoal3,
  map_tac (tinter Tac4') MidGoal4 NewGoal4,
  goalr_tac (and_goal NewGoal3 NewGoal4) NewGoal34,
  goalr_tac (and_goal NewGoal2 NewGoal34) NewGoal23,
  goalr_tac (and_goal NewGoal1 NewGoal23) NewGoal.
tproc (then_tac (try_tac Tac) (pair_tac Tac1'
                              (pair_tac Tac2' Tac3'))) OldGoal NewGoal :-     % open three branches
  not(Tac = then_tac _ _),
  Tac OldGoal (and_goal MidGoal1 (and_goal MidGoal2 MidGoal3)),
  map_tac (tinter Tac1') MidGoal1 NewGoal1,
  map_tac (tinter Tac2') MidGoal2 NewGoal2,
  map_tac (tinter Tac3') MidGoal3 NewGoal3,
  goalr_tac (and_goal NewGoal2 NewGoal3) NewGoal23,
  goalr_tac (and_goal NewGoal1 NewGoal23) NewGoal.
tproc (then_tac (try_tac Tac) (pair_tac Tac1' Tac2')) OldGoal NewGoal :-      % open two branches
  not(Tac = then_tac _ _),
  Tac OldGoal (and_goal MidGoal1 MidGoal2),
  map_tac (tinter Tac1') MidGoal1 NewGoal1,
  map_tac (tinter Tac2') MidGoal2 NewGoal2,
  goalr_tac (and_goal NewGoal1 NewGoal2) NewGoal.
tproc (then_tac (try_tac Tac) Tac') OldGoal NewGoal :-                        % linear tactic
  Tac OldGoal MidGoal, map_tac (tinter Tac') MidGoal NewGoal.
tproc (then_tac (try_tac Tac) Tac') OldGoal NewGoal :-                        % failed tactics
  print_ "--> Tactic failed.", map_tac (tinter Tac') OldGoal NewGoal.

end
