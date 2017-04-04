module basic_tacs.

accumulate compound_tacs.
import frame.

% -----------------------
% rules of Cqk
% -----------------------

tax PosL PosR ((ax PosL PosR) proves (Gamma --> Delta)) true_goal :-
  memberN_ PosL F Gamma, memberN_ PosR F Delta,
  print_ "**** AX (", write_ PosL, print_ " ", write_ PosR, print_ ") closes.\n".

tlnot Pos ((lnot Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma' --> ((Phi at_ Tau)::Delta))),
  F = (not_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-NOT (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trnot Pos ((rnot Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (((Phi at_ Tau)::Gamma) --> Delta')),
  F = (not_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-NOT (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tlimp Pos ((limp Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma' --> ((Phi at_ Tau)::Delta)))
                      (P2 proves (((Psi at_ Tau)::Gamma') --> Delta))),
  F = (Phi imp_ Psi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-IMP (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trimp Pos ((rimp Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (((Phi at_ Tau)::Gamma) --> ((Psi at_ Tau)::Delta'))),
  F = (Phi imp_ Psi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-IMP (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tlall Pos ((lall Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves ((((Phi C) at_ Tau)::Gamma') --> Delta)),
  F = (all_ Phi at_ Tau), 
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma'', append_ F Gamma'' Gamma',
  print_ "**** Left-FORALL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trall Pos ((rall Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal a\ ((P a) proves (Gamma --> (((Phi a) at_ Tau)::Delta')))),
  F = (all_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-FORALL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tlbox Pos ((lbox Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (((Phi at_ Tc)::Gamma') --> Delta))
                      (P2 proves (Gamma' --> ((Tau bef Tc)::Delta)))),
  F = (box_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma'', append_ F Gamma'' Gamma',
  print_ "**** Left-BOX (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trbox Pos ((rbox Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal ta\ ((P ta) proves ((Tau bef ta)::Gamma) --> ((Phi at_ ta)::Delta'))),
  F = (box_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-BOX (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

% derived rules

tliff Pos ((liff Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves ( ((Phi imp_ Psi at_ Tau)::(Psi imp_ Phi at_ Tau)::Gamma') --> Delta)),
  F = (Phi iff_ Psi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-IFF (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

triff Pos ((riff Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((Phi imp_ Psi at_ Tau)::Delta')))
                      (P2 proves (Gamma --> ((Psi imp_ Phi at_ Tau)::Delta')))),
  F = (Phi iff_ Psi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-IFF (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tland Pos ((land Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (((Phi at_ Tau)::(Psi at_ Tau)::Gamma') --> Delta)),
  F = (Phi and_ Psi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-AND (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trand Pos ((rand Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((Phi at_ Tau)::Delta')))
                      (P2 proves (Gamma --> ((Psi at_ Tau)::Delta')))),
  F = (Phi and_ Psi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-AND (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tlor Pos ((lor Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (((Phi at_ Tau)::Gamma') --> Delta))
                      (P2 proves (((Psi at_ Tau)::Gamma') --> Delta))),
  F = (Phi or_ Psi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-OR (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tror Pos ((ror Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> ((Phi at_ Tau)::(Psi at_ Tau)::Delta'))),
  F = (Phi or_ Psi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-OR (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tlsome Pos ((lsome Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal a\ ((P a) proves ((((Phi a) at_ Tau)::Gamma') --> Delta))),
  F = (some_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-EXISTS (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trsome Pos ((rsome Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> (((Phi C) at_ Tau)::Delta'))),
  F = (some_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta'', append_ F Delta'' Delta',
  print_ "**** Right-EXISTS (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tldia Pos ((ldia Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal ta\ ((P ta) proves (((Phi at_ ta)::(Tau bef ta)::Gamma') --> Delta))),
  F = (dia_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-DIAMOND (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trdia Pos ((rdia Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((Phi at_ Tc)::Delta')))
                      (P2 proves (Gamma --> ((Tau bef Tc)::Delta')))),
  F = (dia_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta'', append_ F Delta'' Delta',
  print_ "**** Right-DIAMOND (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

% -----------------------
% automatic
% -----------------------

% --- auto ---
% "regular" auto: fast ordering and allow backtracking

tauto InGoal OutGoal :-
  exhaust_tac ( tax _ _::
                trimp _::tror _::tland _::tliff _::
                tlnot _::trnot _::
                trall _::tlsome _::trbox _::tldia _::
                tlall _::trsome _::tlbox _::trdia _::
                tlimp _::triff _::trand _::tlor _::nil)
  InGoal OutGoal.

% --- autoall ---
% complete tactic: use all tactics with no distinction (used in check_)

tautoall InGoal OutGoal :-
  exhaust_tac ( tax _ _::
                tlnot _::trnot _::tlimp _::trimp _::tlall _::trall _::tlbox _::trbox _::
                tliff _::triff _::tland _::trand _::tlor _::tror _::tlsome _::trsome _::tldia _::trdia _::
                trefleq::tsubeq _::tsubeql _ _::tsubeqr _ _::
                tser::trefl::ttrans::twdir::tsdir::twconn::tsconn _ _::tatom::
              nil)
  InGoal OutGoal.

% --- sauto_fo ---
% "slow" auto first-order: safe ordering, no backtracking, only first-order

tsauto_fo InGoal OutGoal :-
  exhaust_tac ( pre2 tax::
                pre trimp::pre tror::pre tland::pre tliff::
                pre tlnot::pre trnot::
                pre tlimp::pre triff::pre trand::pre tlor::
                pre trall::pre tlsome::
                pre tlall::pre trsome::nil )
  InGoal OutGoal.

end
