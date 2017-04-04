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

tlall Pos ((lallU Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves ((((Phi C) at_ Tau)::Gamma') --> Delta)),
  F = (allU_ Phi at_ Tau), 
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma'', append_ F Gamma'' Gamma',
  print_ "**** Left-FORALL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
tlall Pos ((lallN Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves ((((Phi C) at_ Tau)::Gamma') --> Delta)),
  F = (allN_ Phi at_ Tau), 
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma'', append_ F Gamma'' Gamma',
  print_ "**** Left-FORALL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trall Pos ((rallU Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal a\ ((P a) proves (Gamma --> (((Phi a) at_ Tau)::Delta')))),
  F = (allU_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-FORALL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
trall Pos ((rallN Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal a\ ((P a) proves (Gamma --> (((Phi a) at_ Tau)::Delta')))),
  F = (allN_ Phi at_ Tau),
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
trbox2 Pos Ta ((rbox Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = ((P Ta) proves ((Tau bef Ta)::Gamma) --> ((Phi at_ Ta)::Delta')),
  F = (box_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-BOX (", write_ Pos, print_ ") with ", write_ Ta, print_ " gives: ",
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

tlsome Pos ((lsomeU Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal a\ ((P a) proves ((((Phi a) at_ Tau)::Gamma') --> Delta))),
  F = (someU_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-EXISTS (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
tlsome Pos ((lsomeN Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal a\ ((P a) proves ((((Phi a) at_ Tau)::Gamma') --> Delta))),
  F = (someN_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-EXISTS (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trsome Pos ((rsomeU Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> (((Phi C) at_ Tau)::Delta'))),
  F = (someU_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta'', append_ F Delta'' Delta',
  print_ "**** Right-EXISTS (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
trsome Pos ((rsomeN Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> (((Phi C) at_ Tau)::Delta'))),
  F = (someN_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta'', append_ F Delta'' Delta',
  print_ "**** Right-EXISTS (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tldia Pos ((ldia Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal ta\ ((P ta) proves (((Phi at_ ta)::(Tau bef ta)::Gamma') --> Delta))),
  F = (dia_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-DIAMOND (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
tldia2 Pos Ta ((ldia Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = ((P Ta) proves (((Phi at_ Ta)::(Tau bef Ta)::Gamma') --> Delta)),
  F = (dia_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-DIAMOND (", write_ Pos, print_ ") with ", write_ Ta, print_ " gives: ",
  write_ NewGoal, print_ "\n".

trdia Pos ((rdia Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((Phi at_ Tc)::Delta')))
                      (P2 proves (Gamma --> ((Tau bef Tc)::Delta')))),
  F = (dia_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta'', append_ F Delta'' Delta',
  print_ "**** Right-DIAMOND (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

% -------------------------------
% isolate: a variant of weakening
% -------------------------------

tisol FListL FListR ((isol FListL FListR P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma' --> Delta')),
  reduce_ FListL Gamma Gamma', reduce_ FListR Delta Delta',
  print_ "**** ISOLATION gives: ",
  write_ NewGoal, print_ "\n".

% -----------------------
% entailment
% -----------------------

tent ((ent P) proves (Gamma --> Delta))
     true_goal :-
  entails P Gamma Delta,
  print_ "**** Entailment closes ",
  write_ (Gamma --> Delta), print_ "\n".

% -----------------------
% automatic
% -----------------------

% --- auto ---
% "regular" auto: fast ordering and allow backtracking

tauto InGoal OutGoal :-
  exhaust_tac ( tax _ _::tent::
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
                tluntil _::truntil _::tlboxt _::trboxt _::tlnext _::trnext _::
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

% -----------------------------------
% additional rules to take care of FI
% -----------------------------------

tluntil Pos ((luntil Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal ta\ ((P ta) proves ((Tau bef ta)::(Psi at_ ta)::(boxt_ ta Phi at_ Tau)::Gamma') --> Delta)),
  F = (Phi until_ Psi at_ Tau), 
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-UNTIL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
tluntil2 Pos Ta ((luntil Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = ((P Ta) proves ((Tau bef Ta)::(Psi at_ Ta)::(boxt_ Ta Phi at_ Tau)::Gamma') --> Delta),
  F = (Phi until_ Psi at_ Tau), 
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-UNTIL (", write_ Pos, print_ ") with ", write_ Ta, print_ " gives: ",
  write_ NewGoal, print_ "\n".

truntil Pos ((runtil Pos P1 P2 P3) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (Gamma --> ((Tau bef Tc)::Delta')))
            (and_goal (P2 proves (Gamma --> ((Psi at_ Tc)::Delta')))
                      (P3 proves (Gamma --> ((boxt_ Tc Phi at_ Tau)::Delta'))) )),
  F = (Phi until_ Psi at_ Tau), 
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta'', append_ F Delta'' Delta',
  print_ "**** Right-UNTIL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tlwuntil Pos ((lwuntil Pos P1 P2) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (((box_ Phi at_ Tau)::Gamma') --> Delta))
                      (P2 proves (((Phi until_ Psi at_ Tau)::Gamma') --> Delta))),
  F = (Phi wuntil_ Psi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-WEAK/UNTIL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trwuntil Pos ((rwuntil Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> ((box_ Phi at_ Tau)::(Phi until_ Psi at_ Tau)::Delta'))),
  F = (Phi wuntil_ Psi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-WEAK/UNTIL (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

tlboxt Pos ((lboxt Pos P1 P2 P3) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (and_goal (P1 proves (((Phi at_ Tc)::Gamma') --> Delta))
            (and_goal (P2 proves (Gamma' --> ((Tau bef Tc)::Delta)))
                      (P3 proves (Gamma' --> ((Tc bef Taun)::Delta))) )),
  F = (boxt_ Taun Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma'', append_ F Gamma'' Gamma',
  print_ "**** Left-BOXT (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trboxt Pos ((rboxt Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (forall_goal ta\ ((P ta) proves ((Tau bef ta)::(ta bef Taun)::Gamma) --> ((Phi at_ ta)::Delta'))),
  F = (boxt_ Taun Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-BOXT (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".
trboxt2 Pos Ta ((rboxt Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = ((P Ta) proves ((Tau bef Ta)::(Ta bef Taun)::Gamma) --> ((Phi at_ Ta)::Delta')),
  F = (boxt_ Taun Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-BOXT (", write_ Pos, print_ ") with ", write_ Ta, print_ " gives: ",
  write_ NewGoal, print_ "\n".

tlnext Pos ((lnext Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (((Phi at_ (succ_ Tau))::Gamma) --> Delta')),
  F = (next_ Phi at_ Tau),
  memberN_ Pos F Gamma, deleteN_ Pos Gamma Gamma',
  print_ "**** Left-NEXT (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

trnext Pos ((rnext Pos P) proves (Gamma --> Delta)) NewGoal :-
  NewGoal = (P proves (Gamma --> ((Phi at_ (succ_ Tau))::Delta'))),
  F = (next_ Phi at_ Tau),
  memberN_ Pos F Delta, deleteN_ Pos Delta Delta',
  print_ "**** Right-NEXT (", write_ Pos, print_ ") gives: ",
  write_ NewGoal, print_ "\n".

end
