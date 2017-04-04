module frame.
accumulate compound_tacs.

% -------------------------
% rules for equality (Cqk=)
% -------------------------

trefleq (refleq proves (Gamma --> Delta)) true_goal :-
  memberN_ Y (Tau eqdot Tau) Delta,
  print_ "**** REFL_EQ closes.\n".

tsubeq Pos ((subeq Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (((Tau eqdot Tau')::Gamma') --> Delta')),
  F = (Tau eqdot Tau'),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma_tmp,
  map_ (subst_eqdot Tau Tau') Delta Delta',
  map_ (subst_eqdot Tau Tau') Gamma_tmp Gamma',
  print_ "**** SUB_EQ (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

% --- two tactics which unify the right member of an eqdot with a label
tsubeql Pos Pos' ((subeql Pos Pos' P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> Delta)),
  memberN_ Pos (Phi at_ Tau') Gamma, memberN_ Pos' (Tau eqdot Tau') Gamma,
  print_ "**** SUB_EQ UNIL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
tsubeqr Pos Pos' ((subeqr Pos Pos' P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> Delta)),
  memberN_ Pos (Phi at_ Tau') Delta, memberN_ Pos' (Tau eqdot Tau') Gamma,
  print_ "**** SUB_EQ UNIR (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

subst_eqdot Tau Tau' (Phi at_ Tau) (Phi at_ Tau').
subst_eqdot Tau Tau' (Tau_1 bef Tau) (Tau_1 bef Tau').
subst_eqdot Tau Tau' (Tau bef Tau_1) (Tau' bef Tau_1).
subst_eqdot Tau Tau' (Tau_1 eqdot Tau) (Tau_1 eqdot Tau').
subst_eqdot Tau Tau' (Tau eqdot Tau_1) (Tau' eqdot Tau_1).

% -----------------------
% frame rules
% -----------------------

tser ((ser P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves ((Tau bef (wit Tau))::Gamma) --> Delta),
  print_ "**** SERIALITY gives: ", write_ NewGoal, print_ "\n".

trefl ((refl P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves ((Tau bef Tau)::Gamma) --> Delta),
  print_ "**** REFLEXIVITY gives: ", write_ NewGoal, print_ "\n".

ttrans ((trans P1 P2 P3) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((Tau_0 bef Tau_1)::Delta) ))
            (and_goal (P2 proves (Gamma --> ((Tau_1 bef Tau_2)::Delta) ))
                      (P3 proves (((Tau_0 bef Tau_2)::Gamma) --> Delta)) )),
  print_ "**** TRANSITIVITY gives: ", write_ NewGoal, print_ "\n".

twdir ((wdir P1 P2 P3) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((Tau_0 bef Tau_1)::Delta) ))
            (and_goal (P2 proves (Gamma --> ((Tau_0 bef Tau_2)::Delta) ))
                      (P3 proves (((Tau_1 bef (cv Tau_0 Tau_1 Tau_2))::(Tau_2 bef (cv Tau_0 Tau_1 Tau_2))::Gamma) --> Delta)) )),
  print_ "**** WEAK DIRECTEDNESS gives: ", write_ NewGoal, print_ "\n".

tsdir ((sdir P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (((Tau_1 bef (cv Tau_0 Tau_1 Tau_2))::(Tau_2 bef (cv Tau_0 Tau_1 Tau_2))::Gamma) --> Delta )),
  print_ "**** STRONG DIRECTEDNESS gives: ", write_ NewGoal, print_ "\n".

twconn ((wconn P1 P2 P3 P4 P5) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((T0 bef T1)::Delta) ))
            (and_goal (P2 proves (Gamma --> ((T0 bef T2)::Delta) ))
            (and_goal (P3 proves (((T1 bef T2)::Gamma) --> Delta ))
            (and_goal (P4 proves (((T1 eqdot T2)::Gamma) --> Delta ))
                      (P5 proves (((T2 bef T1)::Gamma) --> Delta )) )))),
  print_ "**** WEAK CONNECTEDNESS gives: ", write_ NewGoal, print_ "\n".

tsconn T1 T2 ((sconn T1 T2 P1 P2 P3) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (((T1 bef T2)::Gamma) --> Delta ))
            (and_goal (P2 proves (((T2 bef T1)::Gamma) --> Delta ))
                      (P3 proves (((T1 eqdot T2)::Gamma) --> Delta )) )),
  print_ "**** STRONG CONNECTEDNESS gives: ", write_ NewGoal, print_ "\n".

tatom ((atom P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (((Tau_0 bef (la Tau_0))::((la Tau_0) eqdot Tau_1)::Gamma) --> Delta))
                      (P2 proves (((Tau_0 bef (la Tau_0))::Gamma) --> (((la Tau_0) bef Tau_1)::Delta))) ),
  print_ "**** ATOMICITY gives: ", write_ NewGoal, print_ "\n".

end
