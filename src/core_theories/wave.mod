/*

File:  wave.mod
Author: Louise Dennis / James Brotherston
Description: Support for Rippling
Last Modified: 20th August 2002

*/

module wave.

accumulate casesplit.

local sinkable_flag etree -> int -> (list int) -> o.
local wcongr_ripple (list etree) -> (list etree) -> (rewrite_rule -> osyn -> osyn -> osyn -> polarity -> o) -> rewrite_rule -> osyn -> osyn -> osyn -> polarity -> (list int) -> (list int) -> o.


local wave_failed  (list preconditions -> o -> ripFail -> o).
local forthose2 list A -> (A -> o) -> list A -> list D -> list D -> o.
local wave_rules_in_hyps (list osyn) -> (list rewrite_rule) -> o.
local wave_rule osyn -> rewrite_rule.


%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Wave Methods
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%


atomic wave (wave_method Dir Rule)
	(seqGoal (Hyps >>> Goal) ((embedding_context E1 _)::T))
	(ripple_rewrite Hyps Rule (Goal @@ E1) (NewGoal @@ E2) Cond TermPos Dir T RDir,
	(trivial_condition Cond Hyps, 
	 (embeds_list E2 NewGoal E3 E1 E1p, 
	 (measure_check Dir E3 E1p TermPos Embedding 2,
	 (for_each_skel Embedding (E\ X\ Y\ sinkable E nil) _ _ skeleton [] [])))))
        (log_rewrite_rule T Rule,
	 mappred Hyps (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce Hyps X Z;
		  Z = X)),
		 B = (hyp Z T))) NewHyps)
	(seqGoal (NewHyps >>> NewGoal) ((embedding_context Embedding Dir)::T))
	notacticyet.



change_method_vars (wave_method Dir Rule) (wave_method Dir _) :- !.



% wave_casesplit_method intended to be invoked by a critic

atomic_critic wave (check_wave_case_split Rule)
	      Address
	      Agenda
	      (get_goal Address (seqGoal (Hyps >>> Conc) E),
	      casesplit_analysis Hyps Conc Rule _ (X\ wave_rule_list X))
	      true
	      nil
	      Agenda.


atomic wave (wave_case_split Rule)
	(seqGoal (Hyps >>> Conc) E)
	(casesplit_analysis Hyps Conc Rule Cases (X\ wave_rule_list X))
	(mapfun Cases (x\ (seqGoal (((hyp x nha)::Hyps) >>> Conc) E)) GoalList,
		list2goal GoalList Outgoals,
		update_gb_context Outgoals NewOutgoals []
		)
	NewOutgoals
	notacticyet.
change_method_vars (wave_case_split Rule) (wave_case_split _):-!.

%%%%%


atomic wave set_up_ripple
         ( seqGoal (H >>> Goal) Context)
         ( 
	induction_hypothesis H Hl OtherHyps, 
	  (%% Beta reduce the goal if necessary
               (congr (R\ P\ LHS\ RHS\ C\ 
               (rewr R P LHS RHS C)) beta_reduction positive_polarity Goal Goal2 _ _ _);
	   (Goal = Goal2)),

	   forthose E (Emb\ IndHyp\ BetaRedHyp\ 
		sigma BRH\
 		(
		 ((%% beta reduce induction hypothesis if necessary
	    	 IndHyp = (hyp Candidate ind_hyp) ,
	   	congr (R\ P\ LHS\ RHS\ C\ 	
               		(rewr R P LHS RHS C)) beta_reduction positive_polarity Candidate C2 _ _ _,
%		 BRH = C2,
		 BetaRedHyp = (hyp C2 ind_hyp));
	         BetaRedHyp = IndHyp),
%                 IndHyp = (hyp BRH ind_hyp)),
%		 embeds Emb BRH Goal2)) Hl FinalIndHyps,
		 strip_forall_embeds BetaRedHyp Emb Goal2)) Hl FinalIndHyps,

	  (not (E = nil)), !,
	   not (member (embedding_context E outward) Context),
	   append OtherHyps FinalIndHyps H2
          )
          true
         (seqGoal (H2 >>> Goal2) ((embedding_context E outward)::Context) )
          notacticyet.



atomic wave post_ripple
         (seqGoal Seq C)
          true 
         (filter C NewCon (Con\ Con = (embedding_context _ _)))
         (seqGoal Seq NewCon) 
         notacticyet.

%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Wave Critics
%%
%%%%%%%%%%%%%%%%%%%%%%%%%

compound_critic wave wave_critic_strat
	(then_crit (pop_critic FailAd)
	(then_crit (subplan_crit FailAd (then_crit (wave_failure Failure Rule)
	 				 open_node))
		   (wave_patch Failure FailAd Rule))).

compound_critic wave (wave_patch (failed_cond Rule) Ad Rule)
	(subplan_crit Ad
		      (then_crit (check_wave_case_split Rule)
	(subplan_crit Ad 
	   (continue_crit (m\ (then_meth (wave_case_split Rule) 
		(map_meth (then_meth (try_meth rewrite_with_hyp) m)))))))).

atomic_critic wave (wave_failure Failure Rule)
	Address
	Agenda
	(get_preconditions Address Pre, 
	 failed_pre Pre Failed,
	 wave_failed Pre Failed Failure)
	true
	nil
	Agenda.

%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Support Predicates
%%
%%%%%%%%%%%%%%%%%%%%%%%


%%%%%
% ripple_rewrite, just 1 step, not assuming that we really have an embedding
% - placing a variable where embedding will change

%version for merging congruency and embeddings 
%  Before is the Goal
%%%%
ripple_rewrite Hyps Rule (Before @@ E1) (Goal2 @@ E2) Cond TermPos Dir Ctext RDir:-
     wave_rules_in_hyps Hyps L,
     wave_rules_list StaticL,
    (((member (banned BList) Ctext), !, partition_rw BList StaticL _ Rest); 
           Rest = StaticL), !,
    append L Rest RL,
     wcongr_ripple E1 E2 
                (R\ X\ Y\ C\ P\ (sigma Emb\ sigma F\ (memb R RL,
%%		((Dir = outward, not (X = (app F _), headvar_osyn F, definition _ R _ _ _));
%%		 (Dir = inout)),
                        ((rewr R positive_polarity X Y C, 
			       ((definition _ R _ _ _, RDir = 1);
			        (RDir = 0)));
                         (rewr R negative_polarity Y X C, RDir = 0)), 
			 env_otype X Hyps _,
			 env_otype Y Hyps _,
                        (not (bad_for_synthesis R Y)),
                        (not (embeds Emb X Y))
)))
                                    Rule Before After Cond P nil TermPos,
	env_otype Before Hyps _,
	collapse_pwfs Hyps After,
        beta_reduce Hyps After Goal2, 
	env_otype Goal2 Hyps _.

%% Check Term is not a metavariable.
wcongr_ripple OldE NewE _Rewr _R X _Y _C _P TermPos _:-
     headvar_osyn X,
     !,
     fail.

wcongr_ripple OldE NewE Rewr R (polar_term XPolarity X) Y Cond Polarity TermPos TOut:-
  (not (headvar_osyn X)),
  multiply_polarities Polarity XPolarity NewPolarity,
  wcongr_ripple OldE NewE Rewr R X Y Cond NewPolarity TermPos TOut.
  

%rewrite applies -- find new embedding
wcongr_ripple OldE NewE Rewr R X Y Cond Polarity TermPos TermPos:-
	copy_term [X] [CleanX],
	count_vars X CleanX 0 N1 XList,
	N is (N1 - 1),
	((make_var_pairs N DBInfo,
	  modify_args CleanX Xdb DBInfo,
	  replace_fs Xdb X1 N1 PairList); 
         (N < 0, DBInfo = [], PairList = [], X1 = X)),
    Rewr R X1 Y Cond Polarity,	
	reinstantiate XList DBInfo PairList,
    mappred OldE remove_positions IntE,
    mappred IntE modify_embedding NewE,
    ((verbose off, !); (verbose on,
    pprint_string "Applicable rewrite rule: ",
    printstdout R)).
%%, printstdout NewE, printstdout "a",	printstdout IntE.

wcongr_ripple OldE NewE Rewr R (abs In Type) (abs Out Type) (abs Cond Type) P TermPos TOut:-
     pi (x:osyn)\ (
	congr_ripple_skel OldE TermPos 0 (NewOldE x) RestE x,
	wcongr_ripple (NewOldE x) (NNewE x) Rewr R (In x) (Out x) (Cond x) P TermPos TOut,	
	reform_emb 0 OldE (NNewE x) RestE NewE x).

wcongr_ripple OldE NewE Rewr R (app F A) (app F NewA) Cond P TermPos Tout:-
    polarise (app F A) PolarA,
    nth PolarA N Arg Rest,
    N1 is N + 1,
    congr_ripple_skel OldE TermPos N1 NewOldE RestE _,
    wcongr_ripple NewOldE NNewE Rewr R Arg NewL Cond P (N1 :: TermPos) Tout,
    mappred Rest unpolarise UnPolarRest,
    nth NewA N  NewL UnPolarRest,
    reform_emb N1 OldE NNewE RestE NewE _.

wcongr_ripple OldE NewE Rewr R (app F A) (app NF A) Cond P TermPos Tout:-
    congr_ripple_skel OldE TermPos 1 NewOldE RestE _,
    wcongr_ripple NewOldE NNewE Rewr R F NF Cond P (1 :: TermPos) Tout,
    reform_emb 1 OldE NNewE RestE NewE _.

local construct_f (list int) -> osyn -> osyn -> (list osyn) -> (list osyn) -> o.
construct_f NList (app G ArgList) G [] TmpArgs:-
	    permutation NList TmpArgs ArgList.
construct_f NList (abs F _) G (_::T) TmpArgs:-
	pi x\ (construct_f Nlist (F x) G T (x::TmpArgs)).
	         
local make_new_rewr (rewrite_rule -> osyn -> osyn -> osyn -> polarity -> o) -> rewrite_rule -> osyn -> osyn -> osyn -> polarity -> osyn -> (list int) -> o.
make_new_rewr Rewr RuleName F (app G Args) NRHS Polarity Cond NList:-
        Rewr RuleName (app G Args) RHS Cond Polarity,
	replace_all_perms RHS F G NList NRHS.

local tpos_c osyn -> etree -> o.
tpos_c F (leaf _ _ F) :-
       obj_atom F, !.
tpos_c (app F Args) (node _ _ Ftree ArgTree) :-
       !, mappred (F::Args) tpos_c (Ftree::ArgTree).
tpos_c (abs F _) (absnode Ftree) :-
       pi x\ (tpos_c (F x) (Ftree x)).

local replace_all_perms osyn -> osyn -> osyn -> (list int) -> osyn -> o.
replace_all_perms Term F G NList Term:- 
       headvar_osyn Term, !.
replace_all_perms Term F G NList Term:- 
       not (subterm_of Term G _), !.
replace_all_perms (app H Args) F G NList (app F NewNewArgs):-
      not (headvar_osyn H),
      H = G, !,
      permutation NList Args NewArgs,
      mappred NewArgs (X\ Y\ replace_all_perms X F G NList Y) NewNewArgs.
replace_all_perms (app H Args) F G NList (app H NewNewArgs):- !,
      mappred Args (X\ Y\ replace_all_perms X F G NList Y) NewNewArgs.
replace_all_perms (abs Term Type) F G NList (abs NewTerm Type):- !,
      pi x\ (replace_all_perms (Term x) F G Nlist (NewTerm x)).

%%% Sinkability
%% sinkable +Etree
%% sinkable_flag Etree -Flag
%
% Checks an embedding for sinks below all inwards wave-fronts.
% Flag set to 1 if sink present, 0 otherwise.
% 2 indicates an inward wave front at a leaf

local sink1 osyn -> osyn.

sinkable E P:-
%	printstdout "h", printstdout E,
	(not (not (E = (leaf _ _ _)))),
	(not (not (E = (node _ _ _ _)))), 
        (not (not (E = (absnode _)))), !, fail.
sinkable E P:-
%	printstdout "i", 
	sinkable_flag E X P, 
%	printstdout  X, 
	(not (X = 2)).

% type 2 sink!!
sinkable_flag (leaf _ _ S) 1 _:-
	not (headvar_osyn S),
	S = (sink1 _).

% Direction at non-sink leaf must be outward
sinkable_flag (leaf outward Pos _) 0 ParentPos:-
	      length ParentPos OD,
	      length Pos Depth,
	      N is (Depth - OD),
	      (N = 1; N = 0).
sinkable_flag (leaf outward Pos _) 1 ParentPos:-
	      length ParentPos OD,
	      length Pos Depth,
	      N is (Depth - OD),
	      N > 1.

sinkable_flag (leaf inward Pos _) 1 PPos:-
	      length PPos OD,
	      length Pos Depth,
	      N is (Depth - OD),
	      N > 2.
sinkable_flag (leaf inward _ _) 2 _.

% At sink leaf set flag to 1.
sinkable_flag (sink _ _ _) 1 _.

sinkable_flag (node Dir Ad (leaf Dir (1::Ad) Fo) [(leaf Dir (2::Ad) Type), (absnode F)]) X P:-
	not (headvar_osyn Fo),
	Fo = forall,
	pi x\ (sinkable_flag (F (sink1 x)) X Ad).

% Inwards wave front
sinkable_flag (node inward Pos F Elist) 1 _:-
	% Check subterm
	((sinkable_flag F 1 Pos);
	(for_one Elist (Y\ (sinkable_flag Y 1 Pos)) _, !)).

sinkable_flag (node inward Pos F Elist) 1 PPos:-
	      length PPos OD,
	      length Pos Depth,
	      N is (Depth - OD),
	      N > 2.

% Outward wave front
sinkable_flag (node outward Pos F Elist) X PPos:-
	      length PPos OD,
	      length Pos Depth,
	      N is (Depth - OD),
	      (N = 1; N = 0),
	for_one (F::Elist) (Y\ (sinkable_flag Y X Pos)) _, !,
	sinkable F Pos,
	for_each_cut Elist (E\ sinkable E Pos).
sinkable_flag (node outward Pos F Elist) 1 PPos:-
	      length PPos OD,
	      length Pos Depth,
	      N is (Depth - OD),
	      N > 1.
sinkable_flag (absnode F) X P:-
	pi x\ (sinkable_flag (F x) X P).


%%%
%
% Wave Failed
% 
%%%

%% wave_failed _ (ripple_rewrite _ _ _ _ _ _ _) failed_rewrite.
wave_failed Pre (trivial_condition _ _) (failed_cond Rule):-
	success_pre Pre (ripple_rewrite _ Rule _ _ _ _ _ _ _),
	success_pre Pre (embeds_list _ _ _ _ _).
wave_failed Pre (embeds_list _ _ _ _ _) (failed_embed Rule):-
	success_pre Pre (trivial_condition _ _),
	success_pre Pre (ripple_rewrite _ Rule _ _ _ _ _ _ _).
%% wave_failed _ (measure_check _ _ _ _ _) failed_measure.
wave_failed Pre (for_each_skel EList (E\ X\ Y\ sinkable E _) _ _ _ _ _) (failed_sink E NewGoal):-
	success_pre Pre (ripple_rewrite _ _ _ (NewGoal @@ _) _ _ _ _ _),
	memb E EList.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% RIPPLING
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


wave_rules_list L :-
        wave_rule_list L, !.

wave_rule_list nil.

/*************************************************************************/
% Support Predicates for Rippling
/*************************************************************************/

%% embeds_list
%% Wrapper for embeds applied to lists.
%% Call used in wave rule: embeds_list E2 Skel NewGoal Skel2 E3 E1 E1p
%% A: Is Partial Embedding Generated by rewriting

%% C: Is the New Goal

%% A2: Is resulting Embedding List
%% E1: Is original Embedding list.
%% E1p: Was last argument filtered embedding list so that correct list
%% gets sent to measure check.
embeds_list A C A2 E1 E1p:- 
	copy_term [C] [C1],
%%	forthose2 A (Emb\ (set_epos Emb C1)) A2 E1 E1p, 

	%% This is almost certainly not the most efficient way
	%% to achieve the desired result - ie. finding all possible
	%% extensions of the embedding while retaining their link
	%% with the previous embedding for measure checking purposes.
	%% 
	%% convoluted mechanism because I only wrote copy_emb (to avoid)
	%% undoable instantiation of the positions in emb late in the
	%% day.  Should be refactored.
	pair_up A E1 PairList,
	findall (Out\ sigma Emb\ sigma E\ sigma Old\ (
		memb [E, Old] PairList,
		copy_emb E Emb,
		set_epos Emb C1,
		Out = [Emb, Old])) PL2,
	pair_up A2 E1p PL2,
	(not (A2 = nil)),
	!.

local copy_emb etree -> etree -> o.
copy_emb (leaf Dir Pos Osyn) (leaf Dir Pos1 Osyn):-
	 not (not (Pos = [])),
	 not (not (Pos = [1])), !.
copy_emb (leaf Dir Pos Osyn) (leaf Dir Pos Osyn).
copy_emb (sink Dir Pos Osyn) (sink Dir Pos1 Osyn):-
	 not (not (Pos = [])),
	 not (not (Pos = [1])), !.
copy_emb (sink Dir Pos Osyn) (sink Dir Pos Osyn).
copy_emb (absnode E) (absnode E1):-
	 pi x\ (copy_emb (E x) (E1 x)).
copy_emb (node Dir Pos Ftree Etree) (node Dir Pos1 Ftree1 Etree1):-
	 not (not (Pos = [])),
	 not (not (Pos = [1])), !,
	 mappred (Ftree::Etree) copy_emb (Ftree1::Etree1).
copy_emb (node Dir Pos Ftree Etree) (node Dir Pos Ftree1 Etree1):-
	 mappred (Ftree::Etree) copy_emb (Ftree1::Etree1).


local pair_up (list A) -> (list A) -> (list (list A)) -> o.
pair_up [] [] [].
pair_up (H1::T1) (H2::T2) ([H1, H2]::T3):-
	pair_up T1 T2 T3.

strip_forall_embeds (hyp (app forall [Type, (abs Prop Type)]) _) Emb Conc:-
	strip_forall_embeds (hyp (Prop (wild_card Type)) _) Emb Conc.
strip_forall_embeds (hyp (app exists [Type, (abs Prop Type)]) _) Emb Conc:-
	strip_forall_embeds (hyp (Prop (witness)) _) Emb Conc.  
strip_forall_embeds (hyp Skel _) Emb Conc:-
	embeds Emb Skel Conc.


%%  Recurse through list of skeletons and embeddings to find
%%  appropriate one(s) 
%%  for modification.  
%%  Save the "rest" of the embedding for remerging later.
%%
%%  This really recurses down a list of skeletons checking they all 
/* congr_ripple_skel A B C D E F:-
	printstdout A,
	printstdout B,
	printstdout C,
	printstdout D,
	printstdout E,
	printstdout F,
	fail.
*/
congr_ripple_skel nil _ _ nil nil _.
congr_ripple_skel ((node _Dir TermPos Ftree Etree)::OldE) TermPos 1 (Ftree::NewOldE) (Etree::RestE) X:-
    !,
    congr_ripple_skel OldE TermPos 1 NewOldE RestE X.
congr_ripple_skel ((node _Dir TermPos Ftree Etree)::OldE) TermPos N (Etree1::NewOldE) ((Ftree::RestEtree)::RestE) X:-
    N > 1,
    !, 
    N1 is (N - 1),
    nth Arg N1 A _Rest,
    nth Etree N1 Etree1 RestEtree,
    congr_ripple_skel OldE TermPos N NewOldE RestE X.
congr_ripple_skel ((absnode E1)::OldE) TermPos 0 ((E1 X)::NewOldE) ([]::RestE) X:- !,
	congr_ripple_skel OldE TermPos 0 NewOldE RestE X.

%% Embedding and skeleton don't match - this embedding isn't an option.
congr_ripple_skel ((node Dir EPos Ftree ETree)::OldE) TermPos Pos ((node Dir EPos Ftree ETree)::NewOldE) ((dummytree::nil)::RestE) X:-
		  reverse (Pos::TermPos) TPR,
		  reverse EPos EPR,
		  list_prefix TPR EPR,
    congr_ripple_skel OldE TermPos Pos NewOldE RestE X.
congr_ripple_skel (E::OldE) TermPos Pos (dummytree::NewOldE) ((E::nil)::RestE) X:-
    congr_ripple_skel OldE TermPos Pos NewOldE RestE X.

local list_prefix (list A) -> (list A) -> o.
list_prefix [] _.
list_prefix (H::T1) (H::T2):-
	    list_prefix T1 T2.

%%
% reform_emb
%%
%% Used to rebuilt the complete embedding by merging those bits that
%% have been changed with those bits that haven't

reform_emb _ nil nil _ nil _.
%% We've lost this embedding.
reform_emb Pos (_O::OldE) (dummytree::NNewE) ((NN::nil)::RestE) (NN::NewE) _:-
    !,
    reform_emb Pos OldE NNewE RestE NewE _.
reform_emb Pos (_O::OldE) (NN::NNewE) ((dummytree::nil)::RestE) (NN::NewE) _:-
    !,
    reform_emb Pos OldE NNewE RestE NewE _.
reform_emb 1 ((node Dir Ad _ _)::OldE) (NN::NNewE) (R::RestE) ((node Dir Ad NN R)::NewE) _:-
    reform_emb 1 OldE NNewE RestE NewE _.
reform_emb N ((node Dir Ad _ _)::OldE) (NN::NNewE) ((R::Resttree)::RestE) ((node Dir Ad R Etree)::NewE) _:-
    N > 1,
    N1 is (N - 1),
    nth Etree N1 NN Resttree,
    reform_emb N OldE NNewE RestE NewE _.
reform_emb 0  ((absnode E)::OldE) ((NN X)::NNewE) ([]::RestE) ((absnode NN)::NewE) X:-
	reform_emb 0 OldE NNewE RestE NewE X.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%	MEASURE CHECKING
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TermPos is the current position within the goal
% First arg is a key to see if we actually need to measure reduce
measure_check Dir ENew EOld TermPos E3 RDir:-  
   not (EOld = nil), 	
   mappred EOld modify_embedding EOldBeta,
   for_each_skel ENew (X\ Y\ Z\ (check_measure_reducing Dir X Y TermPos Z RDir)) EOldBeta E3 skeleton [] [].

local skeleton etree -> osyn -> o.
skeleton (leaf _ _ Osyn) Osyn.
skeleton (sink _ _ Osyn) Osyn.
skeleton (absnode (X\ (F X))) (abs (X\ (Skel X)) _):-
	pi (x\ (skeleton (F x) (Skel x))).
skeleton (node _ _ E EL) (app F Args):-
	mappred (E::EL) skeleton (F::Args).

%% NB.  Assume correct skel is first.
local for_each_skel (list A) -> (A -> B -> C -> o) -> (list B) -> (list C) -> (A -> D -> o) -> (list D) -> (list D) -> o.

% for_each_skel A B C D E F G:- printstdout "b", fail.
for_each_skel [] _ [] [] _ _ []:- !.
for_each_skel (H::T) P (H1::T1) (H2::T2) P1 L Pending:-
	 P H H1 H2, !,
	 P1 H Skel,
	 ((memb_and_rest Skel Pending Rest, P2 = Rest);
	  Pending = P2),
	 for_each_skel T P T1 T2 P1 (Skel::L) P2, printstdout "e".
for_each_skel (H::T) P (_::T1) T2 P1 L Pending:-
	 P1 H Skel,
	 member Skel L, !,
	 for_each_skel T P T1 T2 P1 L Pending.
for_each_skel (H::T) P (_::T1) T2 P1 L Pending:-
	 P1 H Skel,
	 member Skel Pending, !,
	 for_each_skel T P T1 T2 P1 L Pending.
for_each_skel (H::T) P (_::T1) T2 P1 L Pending:-
	 P1 H Skel,
	 for_each_skel T P T1 T2 P1 L (Skel::Pending).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  INDUCTION HYPOTHESIS
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    


induction_hypothesis ( (hyp H ind_hyp) :: T ) ((hyp H ind_hyp):: H1) T2:- 
		     !, induction_hypothesis T H1 T2.
induction_hypothesis ( H :: T) T1 (H::T2):- !, induction_hypothesis T T1 T2.
induction_hypothesis nil nil nil:- !.




forthose2 nil P nil nil nil:- !.
forthose2 (X::L) P (X::Out) (A::AT) (A::BT):- P X, !, forthose2 L P Out AT BT.
forthose2 (X::L) P Out (_::AT) BT:- forthose2 L P Out AT BT, !.

%%%%%%%%%%%%
%% Remove position information from an embedding.
%%%%%%%%%%%%

remove_positions dummytree dummytree.
remove_positions (leaf Dir _ Osyn) (leaf _ _ Osyn).
remove_positions (sink Dir _ Osyn) (sink _ _ Osyn).
remove_positions (absnode E) (absnode E1):-
	pi x\ (remove_positions (E x) (E1 x)).
remove_positions (node Dir _ F A) (node _ _ F1 A1):-
	remove_positions F F1,
	mappred A remove_positions A1.

%%%%%%%
%% Predicates for handling wave rules in the hypothesis.

wave_rules_in_hyps nil nil.
wave_rules_in_hyps ((hyp WR wrule)::H) ((wave_rule WR)::H1):-
		   !, wave_rules_in_hyps H H1.
wave_rules_in_hyps ((hyp WR new_rewrite)::H) ((wave_rule WR)::H1):-
		   !, wave_rules_in_hyps H H1.
wave_rules_in_hyps (H::T) T1:-
		   wave_rules_in_hyps T T1.

rewr (wave_rule (app forall [Type, (abs X Type)])) P LHS RHS Cond:-
     rewr (wave_rule (X Y)) P LHS RHS Cond.
rewr (wave_rule (app eq [LHS, RHS])) _ LHS RHS trueP.


local collapse_pwfs (list osyn) -> osyn -> o.
collapse_pwfs _ X:-
	      headvar_osyn X, !.
collapse_pwfs _ X:-
	      obj_atom X, !.
collapse_pwfs Hyps (abs (X\ (Term X)) Type):- 
	      pi x\ (has_otype embed x Type => collapse_pwfs Hyps (Term x)).
collapse_pwfs Hyps (app F Args):-
	     not (headvar_osyn F), 
	     for_each (F::Args) (collapse_pwfs Hyps).
collapse_pwfs Hyps (app F Args):-
	      headvar_osyn F,
	     for_each (F::Args) (collapse_pwfs Hyps).
collapse_pwfs Hyps (app F Args):-
	      headvar_osyn F,
	      length Args N,
	      projection Hyps (app F Args) N [],
	      for_each Args (collapse_pwfs Hyps).
	      
local projection (list osyn) -> osyn -> int -> (list osyn) -> o.
projection Hyps (app (abs (X\ X) Type) [A]) 1 _:-
	   env_otype A Hyps Type.
projection Hyps (app (abs (X\ Z) Type) [A]) 1 List:-
	member Z List,
	env_otype Z Hyps Type.
projection Hyps (app (abs (X\ (Term X)) Type) (H::T)) N List:-
	N > 1,
	N1 is N - 1,
	env_otype H Hyps Type,
	pi x\ (has_otype embed x Type => projection Hyps (app (Term x) T) N1 (x::List)).

/*
%% Find number of free (app) vars and set up permutation key lists.
local db int -> osyn.
local syn_pair osyn -> (list int) -> (list int) -> osyn.
local make_var_pairs int -> (list osyn) -> o.
make_var_pairs 0 [(syn_pair (db 0) CL F)].
make_var_pairs N ((syn_pair (db N) CL PL)::L):-
	N > 0,
	N1 is (N - 1),
	make_var_pairs N1 L.

local count_vars osyn -> osyn -> int -> int -> (list (list osyn)) -> o.
count_vars _ F N N []:- 
	headvar_osyn F, !.
count_vars _ X N N []:-
	   obj_atom X.
count_vars (app G A) (app F Args) Nin Nout List:-
	   not (headvar_osyn F),
	   map_accum (G::A) (F::Args) count_vars Nin Nout List.
count_vars (app F A) (app (db Nin) Args) Nin Nout ([F, (db Nin)]::List):-
	   Nin2 is (Nin + 1),
	   map_accum A Args count_vars Nin2 Nout List.
count_vars (abs Y Type) (abs X Type) Nin Nout List:-
	   pi (x\ (count_vars (Y x) (X x) Nin Nout List)).

local map_accum (list A) -> (list A) -> (A -> A -> B -> B -> (list (list A)) -> o) -> B -> B -> (list (list A)) -> o.
map_accum nil nil P X X [].
map_accum (H1::T1) (H::T) P Xin Xout List:-
	  P H1 H Xin NewX List1, !,
	  map_accum T1 T P NewX Xout List2,
	  append List1 List2 List.

%% modify the term for rewriting
local modify_args osyn -> osyn -> (list osyn) -> o.
modify_args F F L:-
	headvar_osyn F.
modify_args F F L:-
	not (headvar_osyn F),
	obj_atom F.
modify_args (app (db N) Args) (app (db N) NewArgs) L:-
	memb (syn_pair (db N) CL NumL) L,
	choice CL NumL Args NewArgs.
modify_args (app F Args) (app F1 Args1) L:-
	   not (F = (db _)), 
	   mappred_bt (F::Args) (A\ B\ modify_args A B L) (F1::Args1).
modify_args (abs (X\ (F X)) Type) (abs (X\ (F1 X)) Type) L:-
	pi (x\ (has_otype embed x Type => (modify_args (F x) (F1 x) L))).

local mappred_bt (list A) -> (A -> B -> o) -> (list B) -> o.
mappred_bt nil P nil.
mappred_bt (X::L) P (Y::K) :- 	 
 P X Y, mappred_bt L P K.

local replace_fs osyn -> osyn -> int -> (list (list osyn)) -> o.
replace_fs X X 0 []:- on_backtracking (printstdout "s").
replace_fs Xin XOut N1 ([(db N), F]::L):-
	N1 > 0,
	N is (N1 - 1),
	replace_with Xin (db N) F Xint,		
	replace_fs Xint XOut N L, !, on_backtracking (printstdout "q").

local choice  (list int) -> (list int) -> (list osyn) -> (list osyn) -> o.
choice CombList NList ArgsIn ArgsOut:-
	drop CombList ArgsIn ArgInt,
	not (ArgInt = nil),
	permutation NList ArgInt ArgsOut.

local drop (list int) -> (list A) -> (list A) -> o.
drop [] [] [].
drop (1::N) (H::Lin) (H::Lout):-
	drop N Lin Lout.
drop (0::N) (H::Lin) Lout:-
	drop N Lin Lout.

%% Correctly instantiate lambda terms in original expressions

% instantiate new free vars as dbs
local unify_fs (list (list osyn)) -> o.
unify_fs [].
unify_fs ([A, B]::L):-
	A = B,
	unify_fs L.

% using db info list construct appropriate lambda term.
local recomb (list int) -> (list osyn) -> (list int) -> osyn -> osyn -> o.
recomb CL AL PL F F:-
       for_each CL (X\ (X = 1)),
       for_each PL (X\ (X = 1)), !.
recomb [] ArgList PL (app F Args) F:-
	reverse ArgList RArgList,
	permutation PL RArgList Args.
recomb (1::N) List PL (abs (X\ (F X)) Type) Inst :-
	pi (x\ (has_otype embed x Type => (recomb N (x::List) PL (F x) Inst))).
recomb (0::N) List PL (abs (X\ (F X)) Type) Inst:-
	pi (x\ (has_otype embed x Type => (recomb N List PL (F x)) Inst)).

local reinstantiate (list (list osyn)) -> (list osyn) -> (list (list osyn)) -> o.
reinstantiate [] _ _.
reinstantiate ([F, (db N)]::L) DBInfo DBInsts:-
	memb ([(db N), G]) DBInsts,
	memb (syn_pair (db N) CL PL) DBInfo,
	recomb CL [] PL F G,
	reinstantiate L DBInfo DBInsts, !.
*/
%% As a result of the instantion of meta-variables as
%% \x \y f [y, x] or similar we need to modify embeddings

local etree_to_osyn etree -> osyn.
modify_embedding dummytree dummytree.
modify_embedding (node Dir Ad (leaf DirL AdL X) Etree) (node Dir Ad (leaf DirL AdL X) Etree2):-
	headvar_osyn X, !,
	mappred Etree modify_embedding Etree2.
modify_embedding (node Dir Ad (leaf DirL AdL (abs (X\ (NewTerm X)) _)) (HE::Etree)) Out:-
	!, modify_embedding (node Dir Ad (leaf DirL AdL (NewTerm (etree_to_osyn HE))) Etree) Out.
modify_embedding (node Dir Ad (leaf DirL AdL (app F L)) []) (node Dir Ad (leaf DirL AdL F) L1):- !,
	mappred L (X\ Y\ (X = (etree_to_osyn Y))) L1.
modify_embedding (node Dir Ad (leaf DirL AdL (etree_to_osyn (leaf Dir3 Ad3 X))) []) (leaf Dir Ad4 X):- !.
modify_embedding (node Dir Ad (leaf DirL AdL (etree_to_osyn (sink Dir3 Ad3 X))) []) (sink Dir Ad4 X):- !.
modify_embedding (node Dir Ad (leaf DirL AdL (etree_to_osyn (node Dir3 Ad3 Ftree Etree))) []) (node Dir _ NFtree NEtree):- !,
	mappred (Ftree::Etree) strip_positions (F1::E1),
	mappred (F1::E1) modify_embedding (NFtree::NEtree).
modify_embedding (leaf Dir Ad Syn) (leaf Dir Ad Syn).
modify_embedding (sink Dir Ad Syn) (sink Dir Ad Syn).
modify_embedding (node Dir Ad Ftree Etree) (node Dir Ad NFtree NEtree):-
	mappred (Ftree::Etree) modify_embedding (NFtree::NEtree).
modify_embedding (absnode T) (absnode T2):-
	pi x\ (modify_embedding (T x) (T2 x)).


local strip_positions etree -> etree -> o.
strip_positions (leaf Dir _ Syn) (leaf Dir Ad Syn).
strip_positions (sink Dir _ Syn) (sink Dir Ad Syn).
strip_positions (absnode E) (absnode E1):-
	pi x\ (strip_positions (E x) (E1 x)).
strip_positions (node Dir _ F E) (node Dir Ad F1 E1):-
		mappred (F::E) strip_positions (F1::E1).

end


