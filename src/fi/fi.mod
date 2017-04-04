/* ----------------------------------
File:           fi.mod
Author:         Claudio Castellini
Description:    Feature Interactions
Last Modified:  December 2002
------------------------------------- */

module fi.
accumulate foltl.

% super_silent_mode.
% plan_printing on.
% pds_plan fi_exists_path fi_triv_1.
% claudio_plan fi_exists_path fi_triv_1 P, proofcheck P fi_triv_1.

% --- why does this have to be commented out?
% is_otype fi user [alice] [bob] [charlie].

mymappred2 P nil nil.
mymappred2 P [X|L] [Y|K] :- P X Y, mymappred2 P L K.

disjunct_of Phi Phi.
disjunct_of Phi (Phi or_ Rest).
disjunct_of Phi (Psi or_ Rest) :- disjunct_of Phi Rest.

% --------------------------------------------------------
% Formalizing a finite automaton into FOLTL --- toy system
% --------------------------------------------------------

%
% This system:
% - initially IDLE(0)
% - from IDLE go to (DIALLING(1) or UNAVAILABLE(2)) by OFFHOOK
% - from UNAVAILABLE go back to IDLE by ONHOOK
% - from DIALLING go to CONNECTING(3) by DIAL 
% - from CONNECTING go back to IDLE by ONHOOK
%

% ----- mutual exclusion
name "mutex" (allN_ n\ allN_ m\ allU_ x\ box_ ((at n x) and_ (at m x) imp_ (n eq_ m))).

% ----- state correspondence
name "st_0" (allU_ x\ allU_ y\ allU_ z\ box_ ((idle x) iff_ (at z_ x))).
name "st_1" (allU_ x\ allU_ y\ allU_ z\ box_ ((dialling x) iff_ (at (s_ z_) x))).
name "st_2" (allU_ x\ allU_ y\ allU_ z\ box_ ((unavailable x) iff_ (at (s_ (s_ z_)) x))).
name "st_3" (allU_ x\ allU_ y\ allU_ z\ box_ ((connecting x y) iff_ (at (s_ (s_ (s_ z_))) x))).

% ----- progress formulae
name "prog_0" (allU_ x\ allU_ y\ allU_ z\ box_ ((idle x) imp_ ((idle x) wuntil_ (offhook x)))).
name "prog_1" (allU_ x\ allU_ y\ allU_ z\ box_ ((dialling x) imp_ ((dialling x) wuntil_ (dial x y)))).
name "prog_2" (allU_ x\ allU_ y\ allU_ z\ box_ ((unavailable x) imp_ ((unavailable x) wuntil_ (onhook x)))).
name "prog_3" (allU_ x\ allU_ y\ allU_ z\ box_ ((connecting x y) imp_ ((connecting x y) wuntil_ (onhook x)))).

% ----- transitions
name "trans_0" (allU_ x\ allU_ y\ allU_ z\ box_ ((idle x) and_ (offhook x) imp_ ((next_ (dialling x)) or_ (next_ (unavailable x))))).
name "trans_1" (allU_ x\ allU_ y\ allU_ z\ box_ ((dialling x) and_ (dial x y) imp_ next_ (connecting x y))).
name "trans_2" (allU_ x\ allU_ y\ allU_ z\ box_ ((unavailable x) and_ (onhook x) imp_ next_ (idle x))).
name "trans_3" (allU_ x\ allU_ y\ allU_ z\ box_ ((connecting x y) and_ (onhook x) imp_ next_ (idle x))).

% ----- initial state
name "init" (allU_ x\ allU_ y\ allU_ z\ (idle x)).

% ----- trivial goals (there exists a path)
name "triv_1" (allU_ x\ allU_ y\ allU_ z\ dia_ (idle x)).
name "triv_2" (allU_ x\ allU_ y\ allU_ z\ dia_ (dialling x)).
name "triv_3" (allU_ x\ allU_ y\ allU_ z\ dia_ (someU_ t\ (connecting x t))).

% --------------------------------------------------------
% top goals
% --------------------------------------------------------

% trivial 1: prove that on some path the user eventually goes back to the initial state.

top_goal fi fi_triv_1 Hyps (multi [Phi]) :-
  name "mutex" H0,
  name "st_0" H10, name "st_1" H11, name "st_2" H12, name "st_3" H13,
  name "prog_0" H20, name "prog_1" H21, name "prog_2" H22, name "prog_3" H23,
  name "trans_0" H30, name "trans_1" H31, name "trans_2" H32, name "trans_3" H33,
  name "init" H4,
  name "triv_1" G,
  mymappred2 translate_formula Hyps
             [H0 at_ zero_,
              H10 at_ zero_, H11 at_ zero_, H12 at_ zero_, H13 at_ zero_,
              H20 at_ zero_, H21 at_ zero_, H22 at_ zero_, H23 at_ zero_,
              H30 at_ zero_, H31 at_ zero_, H32 at_ zero_, H33 at_ zero_,
              H4 at_ zero_],
  translate_formula Phi (G at_ zero_).

% trivial 2: prove that on some path the user eventually gets dialling
%            (of course it also works for unavailable)

top_goal fi fi_triv_2 Hyps (multi [Phi]) :-
  name "mutex" H0,
  name "st_0" H10, name "st_1" H11, name "st_2" H12, name "st_3" H13,
  name "prog_0" H20, name "prog_1" H21, name "prog_2" H22, name "prog_3" H23,
  name "trans_0" H30, name "trans_1" H31, name "trans_2" H32, name "trans_3" H33,
  name "init" H4,
  name "triv_2" G,
  mymappred2 translate_formula Hyps
             [H0 at_ zero_,
              H10 at_ zero_, H11 at_ zero_, H12 at_ zero_, H13 at_ zero_,
              H20 at_ zero_, H21 at_ zero_, H22 at_ zero_, H23 at_ zero_,
              H30 at_ zero_, H31 at_ zero_, H32 at_ zero_, H33 at_ zero_,
              H4 at_ zero_],
  translate_formula Phi (G at_ zero_).

% trivial 3: prove that on some path the user eventually
%            tries to connect someone

top_goal fi fi_triv_3 Hyps (multi [Phi]) :-
  name "mutex" H0,
  name "st_0" H10, name "st_1" H11, name "st_2" H12, name "st_3" H13,
  name "prog_0" H20, name "prog_1" H21, name "prog_2" H22, name "prog_3" H23,
  name "trans_0" H30, name "trans_1" H31, name "trans_2" H32, name "trans_3" H33,
  name "init" H4,
  name "triv_3" G,
  mymappred2 translate_formula Hyps
             [H0 at_ zero_,
              H10 at_ zero_, H11 at_ zero_, H12 at_ zero_, H13 at_ zero_,
              H20 at_ zero_, H21 at_ zero_, H22 at_ zero_, H23 at_ zero_,
              H30 at_ zero_, H31 at_ zero_, H32 at_ zero_, H33 at_ zero_,
              H4 at_ zero_],
  translate_formula Phi (G at_ zero_).

% methods

% A method which simulates the E path quantifier in CTL.
% Given a diamond-property PHI to be verified on a path,
%   (i) find a transition with PHI as consequent
%  (ii) try to prove its antecedents
% (iii) find a progress formula with them in it
%  (iv) reach the initial state.

compound fi fi_exists_path
  (complete_meth
    (repeat_meth
      (orelse_meth (fi_prove_init _)
      (orelse_meth (fi_find_cons _) (fi_find_progress _)
  ))))
  _
  true.

% Prove the initial state: if an eventually-formula is required
% to be proved, have it proved if it is in the initial state.

atomic fi (fi_prove_init Pos_)
  (seqGoal (Hyps >>> (multi [G])))
  ( translate_formula G ((allU_ x\ allU_ y\ allU_ z\ dia_ (InitState x y z)) at_ zero_),
    membN Pos G' Hyps,
    translate_formula G' ((allU_ x\ allU_ y\ allU_ z\ (InitState x y z)) at_ zero_) )
  true
  trueGoal
  notacticyet.

% Find the consequent(s) of a transition

atomic fi (fi_find_cons Pos_)
  (seqGoal (Hyps >>> (multi [G])))
  ( translate_formula G ((allU_ x\ allU_ y\ allU_ z\
      dia_ (someU_ t\ (EvtState x y z t))) at_ zero_),
    membN Pos Transition Hyps,
    translate_formula Transition ((allU_ x\ allU_ y\ allU_ z\
      box_ ((CurrState x y z) and_ (Action x y z) imp_ (NextStates x y z))) at_ zero_),
    disjunct_of (next_ (EvtState X Y Z T)) (NextStates X Y Z) )
  ( translate_formula G' ((allU_ x\ allU_ y\ allU_ z\
      dia_ ((CurrState x y z) and_ (Action x y z))) at_ zero_) )
  (seqGoal (Hyps >>> (multi [G'])))
  notacticyet.
atomic fi (fi_find_cons Pos_)
  (seqGoal (Hyps >>> (multi [G])))
  ( translate_formula G ((allU_ x\ allU_ y\ allU_ z\
      dia_ (EvtState x y z)) at_ zero_),
    membN Pos Transition Hyps,
    translate_formula Transition ((allU_ x\ allU_ y\ allU_ z\
      box_ ((CurrState x y z) and_ (Action x y z) imp_ (NextStates x y z))) at_ zero_),
    disjunct_of (next_ (EvtState X Y Z)) (NextStates X Y Z) )
  ( translate_formula G' ((allU_ x\ allU_ y\ allU_ z\
      dia_ ((CurrState x y z) and_ (Action x y z))) at_ zero_) )
  (seqGoal (Hyps >>> (multi [G'])))
  notacticyet.

% Prove the consequent(s) of a transition by means of a progress property

atomic fi (fi_find_progress Pos_)
  (seqGoal (Hyps >>> (multi [G])))
  ( translate_formula G ((allU_ x\ allU_ y\ allU_ z\
      dia_ ((CurrState x y z) and_ (Action x y z))) at_ zero_),
    membN Pos Transition Hyps,
    translate_formula Transition ((allU_ x\ allU_ y\ allU_ z\
      box_ ((CurrState x y z) imp_ ((CurrState x y z) wuntil_ (Action x y z)))) at_ zero_) )
  ( translate_formula G' ((allU_ x\ allU_ y\ allU_ z\
      dia_ (CurrState x y z)) at_ zero_) )
  (seqGoal (Hyps >>> (multi [G'])))
  notacticyet.

end
