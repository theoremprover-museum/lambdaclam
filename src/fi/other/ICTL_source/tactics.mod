module tactics.

import time.

type true_goal     goal.
type and_goal      goal -> goal -> goal.
type forall_goal   (I -> goal) -> goal.

%
% ------------------- basic tactics:
% ------------------- incapsulate plain sequent rules
%

%
% --- closing ---
%

type axiom         formula -> proof.
type axiom_tac     int -> int -> goal -> goal -> o.

axiom_tac _ _
        ((axiom (Phi @ Tau)) proves (Gamma --> Delta))
        true_goal
        :-
        nmember X (Phi @ Tau) Gamma,
        nmember Y (Phi @ Tau') Delta,
        Tau = Tau',
        print "**** ---- ", write (Gamma --> Delta),
        print "\n**** ---- closed by axiom\n".

type entail        o -> proof.
type entail_tac    int -> goal -> goal -> o.

entail_tac _
        ((entail C) proves (Gamma --> Delta))
        true_goal
        :-
        nmember X (constraint C) Delta,
        Gamma entails (constraint C),
%        not(not(Gamma entails (constraint C))),
        print "**** ---- ", write (Gamma --> Delta),
        print "\n**** ---- closed by entailment\n".

%
% --- propositional ---
%

type l_imp         proof -> proof -> proof.
type l_imp_tac     int -> goal -> goal -> o.

l_imp_tac _
        ((l_imp P1 P2) proves (Gamma --> Delta))
        (and_goal (P1 proves (Gamma' --> ((Phi @ Tau)::Delta)))
                  (P2 proves (((Psi @ Tau)::Gamma') --> Delta)))
        :-
        nmember X (Phi imp Psi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-IMP gives: ",
          write ( (and_goal (P1 proves (Gamma' --> ((Phi @ Tau)::Delta)))
                  (P2 proves (((Psi @ Tau)::Gamma') --> Delta))) ),
        nl.

type r_imp         proof -> proof.
type r_imp_tac     int -> goal -> goal -> o.

r_imp_tac _
        ((r_imp P) proves (Gamma --> Delta))
        (P proves (((Phi @ Tau)::Gamma) --> ((Psi @ Tau)::Delta')))
        :-
        nmember Y (Phi imp Psi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-IMP gives: ",
          write (P proves (((Phi @ Tau)::Gamma) --> ((Psi @ Tau)::Delta'))),
        nl.

type l_iff         proof -> proof.
type l_iff_tac     int -> goal -> goal -> o.

l_iff_tac _
        ((l_iff P) proves (Gamma --> Delta))
        (P proves ( ((Phi imp Psi @ Tau)::(Psi imp Phi @ Tau)::Gamma') --> Delta))
        :-
        nmember X (Phi iff Psi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-IFF gives: ",
          write (P proves ( ((Phi imp Psi @ Tau)::(Psi imp Phi @ Tau)::Gamma') --> Delta)),
        nl.

type r_iff         proof -> proof -> proof.
type r_iff_tac     int -> goal -> goal -> o.

r_iff_tac _
        ((r_iff P1 P2) proves (Gamma --> Delta))
        (and_goal (P1 proves (Gamma --> ((Phi imp Psi @ Tau)::Delta')))
                  (P2 proves (Gamma --> ((Psi imp Phi @ Tau)::Delta'))))
        :-
        nmember Y (Phi iff Psi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-IFF gives: ",
          write (and_goal (P1 proves (Gamma --> ((Phi imp Psi @ Tau)::Delta')))
                          (P2 proves (Gamma --> ((Psi imp Phi @ Tau)::Delta')))),
        nl.

type l_and         proof -> proof.
type l_and_tac     int -> goal -> goal -> o.

l_and_tac _
        ((l_and P) proves (Gamma --> Delta))
        (P proves (((Phi @ Tau)::(Psi @ Tau)::Gamma') --> Delta))
        :-
        nmember X (Phi and Psi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-AND gives: ",
          write (P proves (((Phi @ Tau)::(Psi @ Tau)::Gamma') --> Delta)),
        nl.

type r_and         proof -> proof -> proof.
type r_and_tac     int -> goal -> goal -> o.

r_and_tac _
        ((r_and P1 P2) proves (Gamma --> Delta))
        (and_goal (P1 proves (Gamma --> ((Phi @ Tau)::Delta')))
                  (P2 proves (Gamma --> ((Psi @ Tau)::Delta'))))
        :-
        nmember Y (Phi and Psi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-AND gives: ",
          write (and_goal (P1 proves (Gamma --> ((Phi @ Tau)::Delta')))
                  (P2 proves (Gamma --> ((Psi @ Tau)::Delta')))),
        nl.

type l_or          proof -> proof -> proof.
type l_or_tac      int -> goal -> goal -> o.

l_or_tac _
        ((l_or P1 P2) proves (Gamma --> Delta))
        (and_goal (P1 proves (((Phi @ Tau)::Gamma') --> Delta))
                  (P2 proves (((Psi @ Tau)::Gamma') --> Delta)))
        :-
        nmember X (Phi or Psi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-OR gives: ",
          write (and_goal (P1 proves (((Phi @ Tau)::Gamma') --> Delta))
                  (P2 proves (((Psi @ Tau)::Gamma') --> Delta))),
        nl.

type r_or          proof -> proof.
type r_or_tac      int -> goal -> goal -> o.

r_or_tac _
        ((r_or P) proves (Gamma --> Delta))
        (P proves (Gamma --> ((Phi @ Tau)::(Psi @ Tau)::Delta')))
        :-
        nmember Y (Phi or Psi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-OR gives: ",
          write (P proves (Gamma --> ((Phi @ Tau)::(Psi @ Tau)::Delta'))),
        nl.

type l_neg         proof -> proof.
type l_neg_tac     int -> goal -> goal -> o.

l_neg_tac _
        ((l_neg P) proves (Gamma --> Delta))
        (P proves (Gamma' --> ((Phi @ Tau)::Delta)))
        :-
        nmember X (neg Phi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-NOT gives: ",
          write (P proves (Gamma' --> ((Phi @ Tau)::Delta))),
        nl.

type r_neg         proof -> proof.
type r_neg_tac     int -> goal -> goal -> o.

r_neg_tac _
        ((r_neg P) proves (Gamma --> Delta))
        (P proves (((Phi @ Tau)::Gamma) --> Delta'))
        :-
        nmember Y (neg Phi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-NOT gives: ",
          write (P proves (((Phi @ Tau)::Gamma) --> Delta')),
        nl.

type l_forall      i -> proof -> proof.
type l_forall_tac  int -> goal -> goal -> o.

l_forall_tac _
        ((l_forall C P) proves (Gamma --> Delta))
        (P proves ((((Phi C) @ Tau)::Gamma') --> Delta))
        :-
        nmember X (forall Phi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-FORALL gives: ",
          write (P proves ((((Phi C) @ Tau)::Gamma') --> Delta)),
        nl.

type r_forall      (i -> proof) -> proof.
type r_forall_tac  int -> goal -> goal -> o.

r_forall_tac _
        ((r_forall P) proves (Gamma --> Delta))
        (forall_goal a\ ((P a) proves (Gamma --> (((Phi a) @ Tau)::Delta'))))
        :-
        nmember Y (forall Phi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-FORALL gives: ",
          write (forall_goal a\ ((P a) proves (Gamma --> (((Phi a) @ Tau)::Delta')))),
        nl.

type l_exists      (i -> proof) -> proof.
type l_exists_tac  int -> goal -> goal -> o.

l_exists_tac _
        ((l_exists P) proves (Gamma --> Delta))
        (forall_goal a\ ((P a) proves ((((Phi a) @ Tau)::Gamma') --> Delta)))
        :-
        nmember X (exists Phi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-EXISTS gives: ",
          write (forall_goal a\ ((P a) proves ((((Phi a) @ Tau)::Gamma') --> Delta))),
        nl.

type r_exists      i -> proof -> proof.
type r_exists_tac  int -> goal -> goal -> o.

r_exists_tac _
        ((r_exists C P) proves (Gamma --> Delta))
        (P proves (Gamma --> (((Phi C) @ Tau)::Delta')))
        :-
        nmember Y (exists Phi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-EXISTS gives: ",
          write (P proves (Gamma --> (((Phi C) @ Tau)::Delta'))),
        nl.

%
% --- temporal ---
%

type l_next        time -> proof -> proof.
type l_next_tac    int -> goal -> goal -> o.

l_next_tac _
        ((l_next Tau P) proves (Gamma --> Delta))
        (P proves (((Phi @ (s Tau))::Gamma') --> Delta))
        :-
        nmember X (next Phi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-NEXT gives: ",
          write (P proves (((Phi @ (s Tau))::Gamma') --> Delta)),
        nl.

type r_next        time -> proof -> proof.
type r_next_tac    int -> goal -> goal -> o.

r_next_tac _
        ((r_next Tau P) proves (Gamma --> Delta))
        (P proves (Gamma --> ((Phi @ (s Tau))::Delta')))
        :-
        nmember Y (next Phi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-NEXT gives: ",
          write (P proves (Gamma --> ((Phi @ (s Tau))::Delta'))),
        nl.

type l_glob        time -> time -> proof -> proof -> proof.
type l_glob_tac    int -> goal -> goal -> o.

l_glob_tac _
        ((l_glob Tau Tc P1 P2) proves (Gamma --> Delta))
        (and_goal (P1 proves (((Phi @ Tc)::Gamma') --> Delta))
                  (P2 proves (Gamma' --> ((constraint (Tc wafter Tau))::Delta))))
        :-
        nmember X (glob Phi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-ALWAYS gives: ",
          write (and_goal (P1 proves (((Phi @ Tc)::Gamma') --> Delta))
                  (P2 proves (Gamma' --> ((constraint (Tc wafter Tau))::Delta)))),
        nl.

type r_glob        time -> (time -> proof) -> proof.
type r_glob_tac    int -> goal -> goal -> o.

r_glob_tac _
        ((r_glob Tau P) proves (Gamma --> Delta))
        (forall_goal ta\
          ((P ta) proves ((constraint (ta wafter Tau))::Gamma) --> ((Phi @ ta)::Delta')))
        :-
        nmember Y (glob Phi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-ALWAYS gives: ",
          write (forall_goal ta\
             ((P ta) proves ((constraint (ta wafter Tau))::Gamma) --> ((Phi @ ta)::Delta'))),
        nl.

type l_evt          time -> (time -> proof) -> proof.
type l_evt_tac      int -> goal -> goal -> o.

l_evt_tac _
        ((l_evt Tau P) proves (Gamma --> Delta))
        (forall_goal ta\
          ((P ta) proves (((Phi @ ta)::(constraint (ta wafter Tau))::Gamma') --> Delta)))
        :-
        nmember X (evt Phi @ Tau) Gamma,
        ndelete X Gamma Gamma',
        print "**** Left-EVENTUALLY gives: ",
          write (forall_goal ta\
            ((P ta) proves (((Phi @ ta)::(constraint (ta wafter Tau))::Gamma') --> Delta))),
        nl.

type r_evt         time -> time -> proof -> proof -> proof.
type r_evt_tac     int -> goal -> goal -> o.

r_evt_tac _
        ((r_evt Tau Tc P1 P2) proves (Gamma --> Delta))
        (and_goal (P1 proves (Gamma --> ((Phi @ Tc)::Delta')))
                  (P2 proves (Gamma --> ((constraint (Tc wafter Tau))::Delta'))))
        :-
        nmember Y (evt Phi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Right-EVENTUALLY gives: ",
          write (and_goal (P1 proves (Gamma --> ((Phi @ Tc)::Delta')))
                  (P2 proves (Gamma --> ((constraint (Tc wafter Tau))::Delta')))),
        nl.

%
% --- naive induction ---
%

type induc       proof -> (time -> proof) -> time -> proof.
type induc_tac   int -> goal -> goal -> o.

induc_tac _
        ((induc P1 P2 Tau) proves (Gamma --> Delta))
        (and_goal
          (P1 proves (Gamma --> ((Phi @ Tau)::Delta')))
          (forall_goal ta\
            ((P2 ta) proves ((constraint (ta wafter Tau))::(Phi @ ta)::Gamma) -->
                            ((Phi @ (s ta))::Delta'))))
        :-
        nmember Y (glob Phi @ Tau) Delta,
        ndelete Y Delta Delta',
        print "**** Induction gives: ",
        write (and_goal
                (P1 proves (Gamma --> ((Phi @ Tau)::Delta')))
                  (forall_goal ta\
                    ((P2 ta) proves ((constraint (ta wafter Tau))::(Phi @ ta)::Gamma) -->
                    ((Phi @ (s ta))::Delta')))), nl.

%
% ------------------- compound tactics:
% ------------------- enforce conditional, exhaustive, ordered application
% ------------------- of tactics, both basic AND compound
%

%
% --- goalr ---
%
% Simplifies true_goal inside goal constructors
%

type    goalr_tac     goal -> goal -> o.

goalr_tac (and_goal true_goal Goal) OutGoal :- !, goalr_tac Goal OutGoal.
goalr_tac (and_goal Goal true_goal) OutGoal :- !, goalr_tac Goal OutGoal.
goalr_tac (forall_goal t\ true_goal) true_goal :- !.
goalr_tac Goal Goal.

%
% --- map ---
%
% Enforces goal constructors
%

type    map_tac       (goal -> goal -> o) -> goal -> goal -> o.

map_tac Tac true_goal true_goal.
map_tac Tac (and_goal InGoal1 InGoal2) OutGoal :-
  map_tac Tac InGoal1 OutGoal1, map_tac Tac InGoal2 OutGoal2,
  goalr_tac (and_goal OutGoal1 OutGoal2) OutGoal.
map_tac Tac (forall_goal InGoal) OutGoal :-
  pi t\ (map_tac Tac (InGoal t) (OutGoal1 t)),
  goalr_tac (forall_goal OutGoal1) OutGoal.
map_tac Tac InGoal OutGoal :- Tac InGoal OutGoal.

%
% --- id and fail ---
%
% id_tac always succeeds, returning what has been done
% fail_tac always fails
%

type id_tac        goal -> goal -> o.
id_tac Goal Goal.

type fail_tac      goal -> goal -> o.
fail_tac Goal Goal :- print "Backtracking...\n", fail.

%
% --- then ---
%
% compose two tactics, i.e., apply them in cascade
%

type then_tac      (goal -> goal -> o) -> (goal -> goal -> o) -> goal -> goal -> o.
then_tac Tac1 Tac2 InGoal OutGoal :-
  Tac1 InGoal MidGoal, map_tac Tac2 MidGoal OutGoal.

%
% --- orelse and orelse! ---
%
% disjunctive application of two tactics. the ! version
% does not allow backtracking.
%

type orelse_tac    (goal -> goal -> o) -> (goal -> goal -> o) -> goal -> goal -> o.
orelse_tac Tac1 Tac2 InGoal OutGoal :-
  Tac1 InGoal OutGoal; Tac2 InGoal OutGoal.

type orelse!_tac    (goal -> goal -> o) -> (goal -> goal -> o) -> goal -> goal -> o.
orelse!_tac Tac1 Tac2 InGoal OutGoal :-
  Tac1 InGoal OutGoal, !; Tac2 InGoal OutGoal.

%
% --- repeat and repeat_go ---
%
% exhaustively apply Tac until it is no longer possible.
% repeat fails at the end (i.e., if the exhaustive application did not yield
% OutGoal), while repeat_go succeeds and yields what could be done.
%

type repeat_tac    (goal -> goal -> o) -> goal -> goal -> o.
repeat_tac Tac InGoal OutGoal :-
  orelse_tac (then_tac Tac (repeat_tac Tac)) fail_tac InGoal OutGoal.

type repeat_go_tac    (goal -> goal -> o) -> goal -> goal -> o.
repeat_go_tac Tac InGoal OutGoal :-
  orelse_tac (then_tac Tac (repeat_tac Tac)) id_tac InGoal OutGoal.

%
% --- try and complete ---
%
% try: apply Tac and, upon failure, restore initial situation
% complete: apply Tac and try to get true_goal out of it.
%

type try_tac       (goal -> goal -> o) -> goal -> goal -> o.
try_tac Tac InGoal OutGoal :-
  orelse_tac Tac id_tac InGoal OutGoal.

type complete_tac  (goal -> goal -> o) -> goal -> goal -> o.
complete_tac Tac InGoal true_goal :-
  Tac InGoal OutGoal, goalr_tac OutGoal true_goal.

%
% ------------------- automatic compound tactics:
% ------------------- employ sequent rules to death!
%

%
% --- auto ---
%
% "regular" auto: fast ordering and allow backtracking
%

type auto_tac      goal -> goal -> o.

auto_tac InGoal OutGoal :-
  (complete_tac
    (repeat_tac

      (orelse_tac (axiom_tac _ _) (orelse_tac (entail_tac _)      % closing rules

      (orelse_tac (r_imp_tac _)  (orelse_tac (r_or_tac _)         % alpha rules (non-branching)
      (orelse_tac (l_and_tac _)  (orelse_tac (l_iff_tac _)
      (orelse_tac (l_neg_tac _)  (orelse_tac (r_neg_tac _)
      (orelse_tac (l_next_tac _) (orelse_tac (r_next_tac _)

      (orelse_tac (r_forall_tac _) (orelse_tac (l_exists_tac _)   % delta rules (universal)
      (orelse_tac (r_glob_tac _)   (orelse_tac (l_evt_tac _)

      (orelse_tac (l_forall_tac _) (orelse_tac (r_exists_tac _)   % gamma rules (existential)
      (orelse_tac (l_glob_tac _)   (orelse_tac (r_evt_tac _)

      (orelse_tac (l_imp_tac _)    (orelse_tac (r_iff_tac _)      % beta rules (branching)
      (orelse_tac (r_and_tac _)    (l_or_tac _)

    ))))))))))))))))))))))) InGoal OutGoal.

%
% --- sauto ---
%
% "slow" auto: slow ordering, no backtracking
%

type sauto_tac      goal -> goal -> o.

sauto_tac InGoal OutGoal :-
  (complete_tac
    (repeat_tac

      (orelse!_tac (axiom_tac _ _) (orelse!_tac (entail_tac _)      % closing rules

      (orelse!_tac (r_imp_tac _)  (orelse!_tac (r_or_tac _)         % alpha rules (non-branching)
      (orelse!_tac (l_and_tac _)  (orelse!_tac (l_iff_tac _)
      (orelse!_tac (l_neg_tac _)  (orelse!_tac (r_neg_tac _)
      (orelse!_tac (l_next_tac _) (orelse!_tac (r_next_tac _)

      (orelse!_tac (l_imp_tac _)    (orelse!_tac (r_iff_tac _)      % beta rules (branching)
      (orelse!_tac (r_and_tac _)    (orelse!_tac (l_or_tac _)

      (orelse!_tac (r_forall_tac _) (orelse!_tac (l_exists_tac _)   % delta rules (universal)
      (orelse!_tac (r_glob_tac _)   (orelse!_tac (l_evt_tac _)

      (orelse!_tac (l_forall_tac _) (orelse!_tac (r_exists_tac _)   % gamma rules (existential)
      (orelse!_tac (l_glob_tac _)   (r_evt_tac _)

    ))))))))))))))))))))))) InGoal OutGoal.
