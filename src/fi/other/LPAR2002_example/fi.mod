/* ----------------------------------

File: fi.mod
Author: Claudio Castellini
Description: an implementation of Feature Interactions in lclam
             Based on FO-LTL
Last Modified: April 2002

------------------------------------- */

module fi.
accumulate foltl.

% predicates involved in feature interactions. These are atomic formulae

is_otype  fi user          [me] [you].
has_otype fi me            user.
has_otype fi you           user.

has_otype fi has_acr       (user arrow bool).
has_otype fi has_cfbl      (user arrow bool).
has_otype fi idle          (user arrow bool).
has_otype fi onhook        (user arrow bool).
has_otype fi dn_allowed    (user arrow bool).
has_otype fi call_req      ((tuple_type[user,user]) arrow bool).
has_otype fi acr_announce  ((tuple_type[user,user]) arrow bool).
has_otype fi forwarding    ((tuple_type[user,user,user]) arrow bool).

mymappred2 P nil nil.
mymappred2 P (X :: L) (Y :: K) :- P X Y, mymappred2 P L K.

%
% predicates modeling features and invariants.
%

% this takes a formula, with at most three abstracted variables, and
% makes it an invariant: surrounds it with three forall's and box-es it at zero

define_invariant Ax Inv :-
  Inv = (app @ (tuple[
           app box
            (app forall (tuple[user,abs x\
              app forall (tuple[user,abs y\
               app forall (tuple[user,abs z\
                 (Ax x y z)])])])),
         zero])).

%
% this takes four "conditions" (enable/persist/release/discharge) and
% builds the spec of a feature
%

define_feature Feature Phi [E,P,R,D] :-
  is_feature Feature [E,P,R,D],
  Phi' = (x\ y\ z\ (app imp (tuple[E x y z,
                 (app until (tuple[P x y z,
                     app or (tuple[R x y z, D x y z
       ])]))]))),
  define_invariant Phi' Phi.

% ACR: IF ( X has ACR, Y is calling him, Y does not display his number, ) THEN
%         ( Y is calling X ) UNTIL
%         ( X tells Y that ACR is active ) OR
%         ( Y hangs up ).

is_feature acr [
  (x\ y\ z\ app and (tuple[app has_acr x,app and (tuple[app call_req (tuple[y,x]),app neg (app dn_allowed y)])])),
  (x\ y\ z\ app call_req (tuple[y,x])),
  (x\ y\ z\ app acr_announce (tuple[x,y])),
  (x\ y\ z\ app onhook y)
].

% CFBL: IF ( X has CFBL and isn't idle, all calls forwarded to Z have ended, Y is calling X ) THEN
%          ( Y is calling X ) UNTIL
%          ( Y's call to X is forwarded to Z ) OR
%          ( Y hangs up ).

is_feature cfbl [
  (x\ y\ z\ app and (tuple[app has_cfbl x,app and (tuple[
                           app neg (app exists (tuple[user,abs t\ (app forwarding (tuple[t,x,z]))])),
                           app and (tuple[app call_req (tuple[y,x]),
                           app neg (app idle x)])])])),
  (x\ y\ z\ app call_req (tuple[y,x])),
  (x\ y\ z\ app forwarding (tuple[y,x,z])),
  (x\ y\ z\ app onhook y)
].

% SYSTEM AXIOMS: defining incompatibilites
%                among features atomic predicates

system_axioms [
  (x\ y\ z\ app neg (app and (tuple[app acr_announce (tuple[x,y]),app forwarding (tuple[y,x,z])]))),
  (x\ y\ z\ app neg (app and (tuple[app acr_announce (tuple[x,y]),app call_req (tuple[y,x])]))),
  (x\ y\ z\ app neg (app and (tuple[app forwarding (tuple[y,x,z]),app call_req (tuple[y,x])]))),
  (x\ y\ z\ app neg (app and (tuple[app onhook y,app call_req (tuple[y,x])]))),
  (x\ y\ z\ app neg (app and (tuple[app onhook y,app forwarding (tuple[y,x,z])]))) ].

% Now build a top goal

top_goal fi (define_interaction F1 F2) (Phi1::Phi2::SAList) (multi [C']) :-
  define_feature F1 Phi1 [E1,P1,R1,D1],
  define_feature F2 Phi2 [E2,P2,R2,D2],
  C = (x\ y\ z\ (app neg (app and (tuple [E1 x y z,
       app and (tuple [E2 x y z,
       app until (tuple [app and (tuple[P1 x y z,P2 x y z]),
       app and (tuple[app neg (P1 x y z),
       app and (tuple[app neg (P2 x y z),
       app and (tuple[app neg (D1 x y z),app neg (D2 x y z)])])])])])])))),
  define_invariant C C',
  system_axioms SA,
  mymappred2 define_invariant SA SAList.

%
% methods for features
%

strip_invariant X Y Z T (app @ (tuple[(app box (app forall (tuple[user,abs x\ app forall (tuple[user,abs y\ app forall (tuple[user,abs z\
    (Phi x y z)])])]))),zero]))
    (app @ (tuple[Phi X Y Z,T])) :- print "", print "".

atomic fi fi_casesplit
  (seqGoal ( (Phi1::Phi2::Gamma) >>> (multi [C])))
  ( define_feature F1 Phi1 [E1,P1,R1,D1], define_feature F2 Phi2 [E2,P2,R2,D2],
    mymappred2 (strip_invariant _ _ _ _) Gamma Gamma1,
    mymappred2 (strip_invariant _ _ _ _) Gamma Gamma2,
    mymappred2 (strip_invariant _ _ _ _) Gamma Gamma3 )
  true
  ( (seqGoal (((app @ (tuple[P1 X Y Z,T1]))::(app @ (tuple[app or (tuple[R1 X Y Z,D1 X Y Z]),T1]))::
               (app leq (tuple [zero,T1]))::Gamma1) >>> (multi nil)))
    **
    ( (seqGoal (((app @ (tuple[P2 X Y Z,T2]))::(app @ (tuple[app or (tuple[R2 X Y Z,D2 X Y Z]),T2]))::
                 (app leq (tuple [zero,T2]))::Gamma2) >>> (multi nil)))
      **
      (seqGoal (( (app @ (tuple[app or (tuple[R1 X Y Z,D1 X Y Z]),T1])) :: (app @ (tuple[app or (tuple[R2 X Y Z,D2 X Y Z]),T2])) ::
                  (app @ (tuple[app neg (P1 X Y Z),Tc])) :: (app @ (tuple[app neg (D1 X Y Z),Tc])) ::
                  (app @ (tuple[app neg (P2 X Y Z),Tc])) :: (app @ (tuple[app neg (D2 X Y Z),Tc])) ::
                  (app eq (tuple[Tc,T1])) :: (app eq (tuple[Tc,T2])) :: (app leq (tuple[zero,Tc])) :: Gamma3) >>> (multi nil))) ))
  notacticyet.

compound fi fi_propositional
  (repeat_meth
    (orelse_meth (max _ _)
    (orelse_meth (mrimp _) (orelse_meth (mror _) (orelse_meth (mland _) (orelse_meth (mliff _)
    (orelse_meth (mlnot _) (orelse_meth (mrnot _)
    (orelse_meth (mlimp _) (orelse_meth (mriff _) (orelse_meth (mrand _) (mlor _)
  ))))))))))) _ true.

compound fi fi_complete
  (complete_meth
    (repeat_meth
      (orelse_meth fi_casesplit fi_propositional)))
  _
  true.

%
% ---------------------------------------------------- a toy proof translation - but useful!
%

top_goal fi toy_top_goal
  [] (multi [app @ (tuple [app imp (tuple [ppp,ppp]),zero])]).

top_goal fi toy_top_goal1
  [] (multi [app @ (tuple [
                app and (tuple [app imp (tuple [ppp,ppp]),
                                app imp (tuple [ppp,ppp])]),zero])]).

top_goal fi toy_top_goal2
  [] (multi [app @ (tuple [
                app and (tuple [app or (tuple [ppp, app neg ppp]),
                app and (tuple [app or (tuple [ppp, app neg ppp]),
                                app or (tuple [ppp, app neg ppp])])]),zero])]).

atomic fi toy_casesplit
  (seqGoal ( [] >>> (multi [app @ (tuple [app and (tuple [P1,app and (tuple [P2,P3])]),zero])])))
  true
  true
  ( (seqGoal ([] >>> (multi [app @ (tuple [P1,zero])])))
    **
    ( (seqGoal ([] >>> (multi [app @ (tuple [P2,zero])])))
       **
      (seqGoal ([] >>> (multi [app @ (tuple [P3,zero])]))) ))
  (wrap3F_tac (T1\ T2\ T3\ (then_tac (trand _) (pair_tac T1 (then_tac (trand _) (pair_tac T2 T3)))))).

compound fi toy_propositional
  (repeat_meth
    (orelse_meth (max _ _)
    (orelse_meth (mrimp _) (orelse_meth (mror _) (orelse_meth (mland _) (orelse_meth (mliff _)
    (orelse_meth (mlnot _) (orelse_meth (mrnot _)
    (orelse_meth (mlimp _) (orelse_meth (mriff _) (orelse_meth (mrand _) (mlor _)
  ))))))))))) _ true.

compound fi toy_complete
  (complete_meth
    (repeat_meth
      (orelse_meth toy_casesplit toy_propositional)))
  _
  true.

end
