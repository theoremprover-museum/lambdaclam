/* ----------------------------------
File: bridge.mod
Author: Claudio Castellini
Description: A bridge between FTL and lclam
Last Modified: May 2002
------------------------------------- */

module bridge.
accumulate fi.

% super_silent_mode.
% claudio_plan fi_complete (define_interaction acr cfbl) P, proofcheck P (define_interaction acr cfbl).
% claudio_plan toy_complete toy_top_goal P, proofcheck P toy_top_goal.

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
translate_lformula (app neg Phi) (not_ Phi') :- translate_lformula Phi Phi'.
translate_lformula (app imp (tuple[Phi,Psi])) (Phi' imp_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app forall (tuple[Otype,abs Phi])) (all_ Phi') :- pi t\ (translate_lformula (Phi t) (Phi' (wrap_P t))).
translate_lformula (app box Phi) (box_ Phi') :- translate_lformula Phi Phi'.
% derived op's
translate_lformula (app and (tuple[Phi,Psi])) (Phi' and_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app or (tuple[Phi,Psi])) (Phi' or_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app iff (tuple[Phi,Psi])) (Phi' iff_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
translate_lformula (app exists (tuple[Otype,abs Phi])) (some_ Phi') :- pi t\ (translate_lformula (Phi t) (Phi' (wrap_P t))).
translate_lformula (app dia Phi) (dia_ Phi') :- translate_lformula Phi Phi'.
% temporal op's
translate_lformula (app next Phi) (next_ Phi') :- translate_lformula Phi Phi'.
translate_lformula (app boxt (tuple[Tau,Phi])) (boxt_ Tau' Phi') :- translate_theta Tau Tau', translate_lformula Phi Phi'.
translate_lformula (app until (tuple[Phi,Psi])) (Phi' until_ Psi') :- translate_lformula Phi Phi', translate_lformula Psi Psi'.
% atoms (nullary, unary, binary, ternary predicates)
translate_lformula Phi (wrap_SF Phi) :- has_otype _ Phi bool.
translate_lformula (app Phi T) ((wrap_P1 Phi) (wrap_P T)) :- has_otype _ Phi (Otype arrow bool).
translate_lformula (app Phi (tuple[T1,T2])) ((wrap_P2 Phi) (wrap_P T1) (wrap_P T2)) :-
  has_otype _ Phi (tuple_type[Otype,Otype] arrow bool).
translate_lformula (app Phi (tuple[T1,T2,T3])) ((wrap_P3 Phi) (wrap_P T1) (wrap_P T2) (wrap_P T3)) :-
  has_otype _ Phi (tuple_type[Otype,Otype,Otype] arrow bool).
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
  check_ Proof Phi',
  print "\nPlan proofchecked! Proof is:\n\n", term_to_string Proof S5, print S5, print "\n\n".

end
