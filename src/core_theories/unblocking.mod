/*

File:  wave.mod
Author: Louise Dennis
Description: Unblocking Method, taken from the Ripple Book
Created: 10th October 2005

*/

module unblocking.

accumulate wave.

local embeds_below etree -> (list int) -> o.

local wcongr_unblock (list etree) -> (list etree) -> (rewrite_rule -> osyn -> osyn -> osyn -> polarity -> o) -> rewrite_rule -> osyn -> osyn -> osyn -> polarity -> (list int) -> (list int) -> o.

local unblock_rewrite rewrite_rule -> (pairing osyn (list etree)) -> (pairing osyn (list etree)) -> osyn -> (list int) -> o.

atomic unblocking (unblock Rule)
	(seqGoal (H >>> G) [(embedding_context Emb Dir)])
	(unblock_rewrite Rule (G @@ Emb) (NewGoal @@ NewEmb) Cond TermPos,
	 embeds_list NewEmb NewGoal E _ _)
	true
	(seqGoal (H >>> NewGoal) [(embedding_context E Dir)])
	notacticyet.
change_method_vars (unblock Rule) (unblock _):- !.

%%%%%
% unblock_rewrite, perform rewriting in a wave front only.

%version for merging congruency and embeddings 
%  Before is the Goal
%%%%

unblock_rewrite Rule (Before @@ E1) (After @@ E2) Cond TermPos:-
     wave_rules_list RL,
     wcongr_unblock E1 E2 
                (R\ X\ Y\ C\ P\ (sigma Emb\ (memb R RL,
                        ((rewr R positive_polarity X Y C);
                         (rewr R negative_polarity Y X C)),
                        (not (bad_for_synthesis R Y)),
                        (not (embeds Emb X Y))
)))
                                    Rule Before After Cond P nil TermPos.

%% Check Term is not a metavariable.
wcongr_unblock OldE NewE _Rewr _R X _Y _C _P _TermPos _:-
     headvar_osyn X,
     !,fail.

wcongr_unblock OldE NewE Rewr R (polar_term XPolarity X) Y Cond Polarity TermPos TOut:-
  (not (headvar_osyn X)),
  multiply_polarities Polarity XPolarity NewPolarity,
  wcongr_unblock OldE NewE Rewr R X Y Cond NewPolarity TermPos TOut.
  

%rewrite applies -- find new embedding
wcongr_unblock OldE NewE Rewr R X Y Cond Polarity TermPos TermPos:-
    not (for_one OldE (E\ embeds_below E TermPos) _),
    Rewr R X Y Cond Polarity,
    %% Check that this is a wave front.  Nothing in the embedding should
    %% point to any term below TermPos.
    mappred OldE remove_positions NewE,
    printstdout "Applicable rewrite rule: ",
    printstdout R.

wcongr_unblock OldE NewE Rewr R (abs In Type) (abs Out Type) (abs Cond Type) P TermPos TOut:-
     pi x \ (wcongr_unblock OldE NewE Rewr R (In x) (Out x) (Cond x) P TermPos TOut).

wcongr_unblock OldE NewE Rewr R (app F A) (app F NewA) Cond P TermPos Tout:-
    polarise (app F A) PolarA,
    nth PolarA N Arg Rest,
    congr_ripple_skel OldE TermPos N NewOldE RestE _,
    wcongr_unblock NewOldE NNewE Rewr R Arg NewL Cond P (N :: TermPos) Tout,
    mappred Rest unpolarise UnPolarRest,
    nth NewA N NewL UnPolarRest,
    reform_emb N OldE NNewE RestE NewE _.

wcongr_unblock OldE NewE Rewr R (app F A) (app NF A) Cond P TermPos Tout:-
    congr_ripple_skel OldE TermPos 1 NewOldE RestE _,
    wcongr_unblock NewOldE NNewE Rewr R F NF Cond P (1 :: TermPos) Tout,
    reform_emb 1 OldE NNewE RestE NewE _.



%% Base Cases
embeds_below (leaf _ Ad _) TermPos:-
	append X TermPos Ad, !.
embeds_below (sink _ Ad _) TermPos:-
	append X TermPos Ad, !.
embeds_below (node _ Ad _ _) TermPos:-
	append X TermPos Ad, !.

embeds_below (node _ Ad E Etree) TermPos:-
	%% Only bother if TermPos might be below this positions somewhere.
	append X Ad TermPos,
	(embeds_below E TermPos;
         for_one Etree (E\ embeds_below E TermPos) _), !.
embeds_below (absnode E) TermPos:-
	pi x\ (embeds_below (E x) TermPos).

end
