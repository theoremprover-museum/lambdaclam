/* ----------------------------------

File: foltl.mod
Author: Claudio Castellini
Description: Labelled theory of First-Order Linear Temporal
             Logic. Based upon Louise's hol.mod & hol.sig
Last Modified: 18th July 2001

------------------------------------- */

module foltl.
accumulate arithmetic.
accumulate ftl.

% super_silent_mode.
% add_list_to_sym_eval_list [leq1,leq2,leq_ss].
% plan_printing on.
% pds_plan foltl_induction induction1.

%----------------------------------
% Syntax constants
%----------------------------------

has_otype foltl @      ((tuple_type [bool, nat]) arrow lform).

has_otype foltl box    (bool arrow bool).
has_otype foltl dia    (bool arrow bool).
has_otype foltl next   (bool arrow bool).
has_otype foltl boxt   ((tuple_type [nat, bool]) arrow bool).
has_otype foltl until  ((tuple_type [bool, bool]) arrow bool).
has_otype foltl wuntil ((tuple_type [bool, bool]) arrow bool).

%----------------------------------
% Definitions, lemmata, axioms
%----------------------------------

lemma foltl leq_1 equiv trueP (app leq (tuple [zero, _])) trueP.
lemma foltl leq_2 equiv trueP (app leq (tuple [app s X,app s Y])) (app leq (tuple [X,Y])).

%----------------------------------
% a wee util
%----------------------------------

membN 1 X [X|L].
membN N X [Y|L] :- !, membN N1 X L, N is N1 + 1.

%----------------------------------
% Atomic methods
%----------------------------------

% ---- basic

atomic foltl (max PosL PosR)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (membN PosL Phi Gamma, membN PosR Phi Delta);
    (membN PosL falseP Gamma); (membN PosR trueP Delta) )
  true
  trueGoal
  (wrap_tac (tax PosL PosR)).

atomic foltl (mlnot Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app neg Phi, Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true 
  (seqGoal (Gamma' >>> (multi ((app @ (tuple [Phi,Tau]))::Delta))))
  (wrap_tac (tlnot Pos)).

atomic foltl (mrnot Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app neg Phi, Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true 
  (seqGoal (((app @ (tuple [Phi,Tau]))::Gamma) >>> (multi Delta')))
  (wrap_tac (trnot Pos)).

atomic foltl (mlimp Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app imp (tuple [Phi,Psi]),Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  ( (seqGoal (((app @ (tuple [Psi, Tau]))::Gamma') >>> (multi Delta))) **
    (seqGoal (Gamma' >>> (multi ((app @ (tuple [Phi, Tau]))::Delta)))) )
  (wrap_tac (tlimp Pos)).

atomic foltl (mrimp Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app imp (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true 
  (seqGoal (((app @ (tuple [Phi,Tau]))::Gamma) >>> (multi ((app @ (tuple [Psi,Tau]))::Delta'))))
  (wrap_tac (trimp Pos)).

atomic foltl (mlall Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app forall (tuple [Otype, (abs Phi)]),Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  (existsGoal Otype (Y\ (seqGoal ( ((otype_of Y Otype)::(app @ (tuple [Phi Y,Tau]))::Gamma') >>> (multi Delta)))))
  (wrap_tac (tlall Pos)).

atomic foltl (mrall Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app forall (tuple [OType, (abs Phi)]),Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true 
  (allGoal OType Y\ (seqGoal (((otype_of Y OType)::Gamma) >>> (multi ((app @ (tuple [(Phi Y),Tau]))::Delta')))))
  (wrap_tac (trall Pos)).

atomic foltl (mlbox Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app box Phi,Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  (existsGoal nat Tc\ ( (seqGoal (((app @ (tuple [Phi, Tc]))::Gamma') >>> (multi Delta))) **
      (seqGoal (Gamma' >>> (multi ((app leq (tuple [Tau, Tc]))::Delta)))) ))
  (wrap_tac (tlbox Pos)).

atomic foltl (mrbox Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app box Phi,Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true
  (allGoal nat ta\ (seqGoal (((app leq (tuple [Tau, ta]))::Gamma) >>> (multi ((app @ (tuple [Phi, ta]))::Delta')))))
  (wrap_tac (trbox Pos)).

% ---- derived

atomic foltl (mland Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app and (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true 
  (seqGoal (( ((app @ (tuple [Phi,Tau]))::(app @ (tuple [Psi,Tau]))::Gamma') >>> (multi Delta))))
  (wrap_tac (tland Pos)).

atomic foltl (mrand Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app and (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true
  ( (seqGoal (Gamma >>> (multi ((app @ (tuple [Phi,Tau]))::Delta')))) **
    (seqGoal (Gamma >>> (multi ((app @ (tuple [Psi,Tau]))::Delta')))) )
  (wrap_tac (trand Pos)).

atomic foltl (mlor Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app or (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  ( (seqGoal (((app @ (tuple [Phi,Tau]))::Gamma') >>> (multi Delta))) **
    (seqGoal (((app @ (tuple [Psi,Tau]))::Gamma') >>> (multi Delta))) )
  (wrap_tac (tlor Pos)).

atomic foltl (mror Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app or (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true 
  (seqGoal ((Gamma >>> (multi ((app @ (tuple [Phi,Tau]))::(app @ (tuple [Psi,Tau]))::Delta')))))
  (wrap_tac (tror Pos)).

atomic foltl (mliff Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app iff (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true 
  (seqGoal (( ((app @ (tuple [app imp (tuple [Phi,Psi]), Tau]))::
      (app @ (tuple [app imp (tuple [Psi,Phi]), Tau]))::Gamma') >>> (multi Delta))))
  (wrap_tac (tliff Pos)).

atomic foltl (mriff Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app iff (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true
  ( (seqGoal (Gamma >>> (multi ((app @ (tuple [app imp (tuple [Phi,Psi]), Tau]))::Delta')))) **
    (seqGoal (Gamma >>> (multi ((app @ (tuple [app imp (tuple [Psi,Phi]), Tau]))::Delta')))) )
  (wrap_tac (triff Pos)).

atomic foltl (mlsome Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app exists (tuple [Otype, (abs Phi)]),Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  (allGoal Otype Y\ (seqGoal (((app @ (tuple [(Phi Y),Tau]))::(otype_of Y Otype)::Gamma') >>> (multi Delta))))
  (wrap_tac (tlsome Pos)).

atomic foltl (mrsome Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app exists (tuple [Otype, (abs Phi)]),Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true 
  (existsGoal Otype (Y\ (seqGoal ( ((otype_of Y Otype)::Gamma) >>> (multi ((app @ (tuple [Phi Y,Tau]))::Delta'))))))
  (wrap_tac (trsome Pos)).

atomic foltl (mldia Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app dia Phi,Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  (allGoal nat ta\ (seqGoal (((app leq (tuple [Tau, ta]))::(app @ (tuple [Phi, ta]))::Gamma') >>> (multi Delta))))
  (wrap_tac (tldia Pos)).

atomic foltl (mrdia Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app dia Phi,Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true
  (existsGoal nat Tc\ ( (seqGoal (Gamma >>> (multi ((app @ (tuple [Phi, Tc]))::Delta')))) **
      (seqGoal (Gamma >>> (multi ((app leq (tuple [Tau, Tc]))::Delta'))))))
  (wrap_tac (trdia Pos)).

% ---- temporal

atomic foltl (mlnext Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app next Phi,Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  (seqGoal (((app @ (tuple [Phi,app s Tau]))::Gamma') >>> (multi Delta)))
  (wrap_tac (tlnext Pos)).

atomic foltl (mrnext Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app next Phi,Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true
  (seqGoal (Gamma >>> (multi ((app @ (tuple [Phi,app s Tau]))::Delta'))))
  (wrap_tac (trnext Pos)).

atomic foltl (mluntil Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app until (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  (allGoal OType Y\ (seqGoal (((app leq (tuple[(app s Tau),Y]))::
                               (app @ (tuple[Psi,Y]))::
                               (app @ (tuple[app boxt (tuple[Y,Phi]),Tau]))::Gamma') >>> (multi Delta))))
  (wrap_tac (tluntil Pos)).

atomic foltl (mruntil Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app until (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true
  (existsGoal nat Tc\ (
    ( (seqGoal (Gamma >>> (multi ((app leq (tuple [app s Tau,Tc]))::Delta')))) **
      ( (seqGoal (Gamma >>> (multi ((app @ (tuple [Psi,Tc]))::Delta')))) **
        (seqGoal (Gamma >>> (multi ((app @ (tuple [app boxt (tuple [Tc,Psi]),Tau]))::Delta')))) ) ) ))
  (wrap_tac (truntil Pos)).

atomic foltl (mlwuntil Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app wuntil (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  ( (seqGoal (((app @ (tuple [app box Phi,Tau]))::Gamma') >>> (multi Delta))) **
    (seqGoal (((app @ (tuple [app until (tuple[Phi,Psi]),Tau]))::Gamma') >>> (multi Delta))) )
  (wrap_tac (tlor Pos)).

atomic foltl (mrwuntil Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app wuntil (tuple [Phi,Psi]), Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true 
  (seqGoal ((Gamma >>> (multi ((app @ (tuple [app box Phi,Tau]))::
                               (app @ (tuple [app until (tuple[Phi,Psi]),Tau]))::Delta')))))
  (wrap_tac (tror Pos)).

atomic foltl (mlboxt Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app boxt (tuple[Tau_n,Phi]),Tau]))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  (existsGoal nat Tc\
    ( (seqGoal (((app @ (tuple [Phi,Tc]))::Gamma') >>> (multi Delta))) **
      ( (seqGoal (Gamma >>> (multi ((app leq (tuple [Tau,Tc]))::Delta)))) **
        (seqGoal (Gamma >>> (multi ((app leq (tuple [app s Tc,Tau_n]))::Delta)))) ) ))
  (wrap_tac (tlboxt Pos)).

atomic foltl (mrboxt Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app @ (tuple [app boxt (tuple[Tau_n,Phi]),Tau]))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true
  (allGoal OType Y\ (seqGoal (((app leq (tuple[Tau,Y]))::
                               (app leq (tuple[app s Y,Tau_n]))::Gamma') >>>
                               (multi ((app @ (tuple [Phi,Y]))::Delta)))))
  (wrap_tac (trboxt Pos)).

atomic foltl (mlleq Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app leq (tuple[Tau,Tau']))),
    (membN Pos F Gamma),
    (replace_in_hyps Gamma F nil Gamma') )
  true
  ( (seqGoal (((app eq (tuple[Tau,Tau']))::Gamma') >>> (multi Delta))) **
    (seqGoal (((app leq (tuple[app s Tau,Tau']))::Gamma') >>> (multi Delta))) )
  (wrap_tac (tlor Pos)).

atomic foltl (mrleq Pos)
  (seqGoal (Gamma >>> (multi Delta)))
  ( (F = (app leq (tuple[Tau,Tau']))),
    (membN Pos F Delta),
    (replace_in_hyps Delta F nil Delta') )
  true 
  (seqGoal ((Gamma >>> (multi ((app eq (tuple[Tau,Tau']))::(app leq (tuple[app s Tau,Tau']))::Delta')))))
  (wrap_tac (tror Pos)).

%----------------------------------
% Frame methods
%----------------------------------

atomic foltl mrefl
  (seqGoal (Gamma >>> (multi Delta)))
  (memb (app leq (tuple [A,A])) Delta)
  true 
  trueGoal 
  (wrap_tac trefl).

atomic foltl mtrans
  (seqGoal (Gamma >>> (multi Delta)))
  ( F1 = (app leq (tuple [A,B])), F2 = (app leq (tuple [B,C])),
    memb F1 Gamma, memb F2 Gamma,
    replace_in_hyps Gamma F1 [app leq (tuple [A,C])] Gamma'', replace_in_hyps Gamma'' F2 nil Gamma' )
  true 
  (seqGoal (Gamma' >>> (multi Delta)))
  (wrap_tac ttrans).

atomic foltl (msconn (wrapTheta T1) (wrapTheta T2))
  (seqGoal (Gamma >>> (multi Delta)))
  true
  true 
  ( (seqGoal (((app lt (tuple [(wrapTheta T1),(wrapTheta T2)]))::Gamma) >>> (multi Delta))) **
    ( (seqGoal (((app lt (tuple [(wrapTheta T2),(wrapTheta T1)]))::Gamma) >>> (multi Delta))) **
      (seqGoal (((app eq (tuple [(wrapTheta T1),(wrapTheta T2)]))::Gamma) >>> (multi Delta))) ) )
  (wrap_tac (tsconn T1 T2)).

%----------------------------------
% Compound methods
%----------------------------------

compound foltl foltl_taut
  (repeat_meth
    (orelse_meth (max _ _)
    (orelse_meth (mrimp _) (orelse_meth (mror _) (orelse_meth (mland _) (orelse_meth (mliff _)
    (orelse_meth (mlnot _) (orelse_meth (mrnot _)
    (orelse_meth (mlimp _) (orelse_meth (mriff _) (orelse_meth (mrand _) (orelse_meth (mlor _)
    (orelse_meth (mrall _) (orelse_meth (mlsome _) (orelse_meth (mruntil _)
    (orelse_meth (mlall _) (mrsome _)
  )))))))))))))))) _ true.

%----------------------------------
% Pretty printing
%----------------------------------

prettify_special (multi T) (blo 1 [PT]) :-
  !, prettify_term_list2 T PT.

prettify_special (app @ (tuple [A,B])) (blo 1 [AA, str " @", brk 1, BB] ) :-
  !, prettify_term A AA, prettify_term B BB.

prettify_special (app box A) (blo 1 [str "[] ", AA ]) :-
  !, prettify_term A AA.
prettify_special (app dia A) (blo 1 [str "<> ", AA ]) :-
  !, prettify_term A AA.
prettify_special (app next A) (blo 1 [str "() ", AA ]) :-
  !, prettify_term A AA.
prettify_special (app until (tuple [A,B])) (blo 1 [AA, str " U", brk 1, BB] ) :-
  !, prettify_term A AA, prettify_term B BB.
prettify_special (app wuntil (tuple [A,B])) (blo 1 [AA, str " W", brk 1, BB] ) :-
  !, prettify_term A AA, prettify_term B BB.
prettify_special (app iff (tuple [A,B])) (blo 1 [AA, str " iff", brk 1, BB] ) :-
  !, prettify_term A AA, prettify_term B BB.

prettify_special (app eq (tuple [A,B])) (blo 1 [AA, str "=", BB] ) :-
  !, prettify_term A AA, prettify_term B BB.
prettify_special (app lt (tuple [A,B])) (blo 1 [AA, str "<", BB] ) :-
  !, prettify_term A AA, prettify_term B BB.
prettify_special (app leq (tuple [A,B])) (blo 1 [AA, str "<=", BB] ) :-
  !, prettify_term A AA, prettify_term B BB.
prettify_special (app plus (tuple [A,B])) (blo 1 [str "(", AA, str "+", BB, str ")"] ) :-
  !, prettify_term A AA, prettify_term B BB.

% ---- this bit is cut'n'pasted from theories/theory_db.mod

local prettify_term_list2 (list osyn) -> thing -> o.

prettify_term_list2 [T] (blo 0 [PT]) :- !,  prettify_term T PT.
prettify_term_list2 [H|Rest] (blo 0 [PH, str ",", brk 1| PRest]) :- !,
         prettify_term H PH,
         prettify_term_list2 Rest (blo _ PRest).

end
