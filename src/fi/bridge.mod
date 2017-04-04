/* ----------------------------------
File: bridge.mod
Author: Claudio Castellini
Description: A bridge between FTL and lclam
Last Modified: May 2002
------------------------------------- */

module bridge.
accumulate fi.

lfvar X :- not(not(X = lfconst1)), not(not(X = lfconst2)).
osynvar X :- not(not(X = osynconst1)), not(not(X = osynconst2)).

% -----------------------------------
% the "bridge"
% -----------------------------------

% ---------------------- translating a CPlan into an FTL tactic
% terminal case
translate_plan (c_and_node _ _ (max N M) _) (tax N M).
% three-branch case
translate_plan (c_and_node _ _ Method [c_and_node _ _ nomethodyet [CPlan1,c_and_node _ _ nomethodyet [CPlan2,CPlan3]]])
               (Tactic Rot1 Rot2 Rot3) :- !,
  atomic _ Method _ _ _ _ (wrap3F_tac Tactic), translate_plan CPlan1 Rot1, translate_plan CPlan2 Rot2, translate_plan CPlan3 Rot3.
% atomic case
translate_plan (c_and_node _ _ Method [CPlan]) (then_tac Tactic Rot) :- !,
  atomic _ Method _ _ _ _ (wrap_tac Tactic), translate_plan CPlan Rot.
% two-branch case
translate_plan (c_and_node _ _ Method [CPlan1,CPlan2]) (pair_tac Rot1 Rot2) :- !,
  translate_plan CPlan1 Rot1, translate_plan CPlan2 Rot2.

% ---------------------- translating a formula in lclam into a formula in FTL
% labelled formulae
translate_formula (app @ (tuple[Phi,Tau])) (Phi' at_ Tau') :- translate_theta Tau Tau', translate_lformula Phi Phi'.
% logical formulae - basic op's
% DANGEROUS!! --- translate_lformula (wrapAtom Phi) Phi :- lfvar Phi.
translate_lformula (app neg Phi) (not_ Phi') :- translate_lformula Phi Phi'.
translate_lformula (app imp (tuple[Phi,Psi])) (Phi' imp_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app forall (tuple[user,abs Phi])) (allU_ Phi') :- pi t\ (translate_lformula (Phi (wrapIota t)) (Phi' t)).
translate_lformula (app forall (tuple[nat,abs Phi])) (allN_ Phi') :- pi t\ (translate_lformula (Phi (wrapIota t)) (Phi' t)).
translate_lformula (app box Phi) (box_ Phi') :- translate_lformula Phi Phi'.
% derived op's
translate_lformula (app and (tuple[Phi,Psi])) (Phi' and_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app or (tuple[Phi,Psi])) (Phi' or_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app iff (tuple[Phi,Psi])) (Phi' iff_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app exists (tuple[user,abs Phi])) (someU_ Phi') :- pi t\ (translate_lformula (Phi (wrapIota t)) (Phi' t)).
translate_lformula (app exists (tuple[nat,abs Phi])) (someN_ Phi') :- pi t\ (translate_lformula (Phi (wrapIota t)) (Phi' t)).
translate_lformula (app dia Phi) (dia_ Phi') :- translate_lformula Phi Phi'.
% temporal op's
translate_lformula (app next Phi) (next_ Phi') :- translate_lformula Phi Phi'.
translate_lformula (app boxt (tuple[Tau,Phi])) (boxt_ Tau' Phi') :- translate_theta Tau Tau', translate_lformula Phi Phi'.
translate_lformula (app until (tuple[Phi,Psi])) (Phi' until_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app wuntil (tuple[Phi,Psi])) (Phi' wuntil_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
% atoms
translate_lformula (app (wrapAtom1 Phi) (wrapIota T)) (Phi T).
translate_lformula (app (wrapAtom2 Phi) (tuple[(wrapIota T1),(wrapIota T2)])) (Phi T1 T2).
translate_lformula (app (wrapAtom3 Phi) (tuple[(wrapIota T1),(wrapIota T2),(wrapIota T3)])) (Phi T1 T2 T3).
translate_lformula (wrapAtom Phi) Phi.
% labels (basically just successor and zero)
translate_theta (app s Phi) (succ_ Phi') :- translate_theta Phi Phi'.
translate_theta zero zero_.
translate_theta Tau Tau' :- has_otype _ Tau nat.

% proof check a plan for a query via FTL:

convHyps [] trueP.
convHyps [app @ (tuple[H1,zero]),app @ (tuple[H2,zero])] (app and (tuple [H1,H2])).
convHyps [app @ (tuple[H,zero])|Tail] (app and (tuple [H,Phi])) :- convHyps Tail Phi.

proofcheck CPlan Query :-
  top_goal _ Query Hyps (multi [app @ (tuple[Phi,zero])]),
  translate_plan CPlan Tactic,
  ( ( not (Hyps = []),
      convHyps Hyps Hyps',
      translate_formula (app @ (tuple[app imp (tuple [Hyps',Phi]),zero])) Phi');
    translate_formula (app @ (tuple[Phi,zero])) Phi'),
  print_ "\n\nFormula was:\n\n",
  write_ Phi',
  print_ "\n\nTactic is:\n\n",
  write_ Tactic,
  print_ "\n\n".
%  check_ Proof Phi',
%  print "\nPlan proofchecked! Proof is:\n\n", term_to_string Proof S5, print S5, print "\n\n".

end
