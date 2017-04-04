/*

File: wave_critics.mod
Author: Louise Dennis / James Brotherston
Description: Induction engine including Andrew Ireland's critics  '
Last Modified: 21st August 2002

*/

module wave_critics.

accumulate induction.

local member_quant goal -> goal -> o.
local is_quantifier_in osyn -> int -> int -> o.
local unsinkable_flag int -> etree -> (list int) -> (list int) -> o.
local quantify_lemma (list osyn) -> osyn -> osyn -> o.
local partial_wave_rule_match goal -> goal -> rewrite_rule -> o.
local place_meta_vars osyn -> etree -> osyn -> (list int) -> int -> o.
local revise_induction goal -> scheme -> subst -> rewrite_rule -> goal -> scheme -> o.
local repeat_ripple_in goal -> goal -> rewrite_rule -> o.
local reverse_directions etree -> etree -> o.
local find_nearest_meth meth -> (list int) -> (list int) -> o.
local find_previous_meth meth -> (list int) -> (list int) -> o.
local parent_address (list int) -> (list int) -> o.
local construct_generalisation goal -> etree -> osyn -> osyn -> o.
local construct_gen_terms osyn -> osyn -> osyn -> osyn -> (list int) -> osyn -> int -> o.
local gen_term osyn -> osyn -> osyn -> osyn -> o.
local iterate_wave_fronts  osyn -> osyn -> osyn -> osyn -> o.

local fully_rippled etree -> (list int) -> o.

%% Induction Revision Critic

%%% ---- Critic code

%% Needs to be failed measure because otherwise you can always
%% rewrite back in with a wave rule that should have rewritten 
%% outwards

/*
compound_critic wave (wave_patch (failed_measure) Ad _Rule)
        (subplan_crit Ad
        (then_crit 
                (induction_revision (induction_meth _I Scheme Subst) Node) 
	(subplan_crit Node
		(continue_crit 
	       (m\ (then_meth (then_meths (induction_meth with_critics Scheme Subst)
               (pair_meth (map_meth (step_case with_critics)) (map_meth id_meth)) ) (induction_top with_critics))))))).
*/

atomic_critic wave (induction_revision (induction_meth _ Scheme Subst) Node)
	Address
	Agenda
	(get_goal Address G,
	 partial_wave_rule_match G NG Rule)
	(find_nearest_meth (induction_meth _ Sc _) Address Node,
	 get_goal Node Goal,
	revise_induction NG Scheme Subst Rule Goal Sc)
	nil
	Agenda.


%%% ---- Support Predicates


partial_wave_rule_match (seqGoal (Hyps >>> Conc)  [(embedding_context Emb _)]) (seqGoal (Hyps >>> NewConc) [(embedding_context Es Dir)]) Rule:-
        memb E Emb,
        place_meta_vars Conc E NewConc nil 0,
        induction_hypothesis Hyps H _,
        embeds_list Es NewConc NewEs _ _,
%	This bit can succeed by enlarging instead of moving the wave front.
%	We want the wave front to move.
        ripple_rewrite Hyps Rule (NewConc @@ NewEs ) (Temp @@ NewE) _ TermPos _ [] RDir,
	embeds_list NewE Temp Embedding Es Esp,
        measure_check Dir Esp NewEs TermPos Embedding RDir.
%	This bit can succeed by enlarging instead of moving the wave front.
%	We want the wave front to move.
%	mappred Es wave_front_moved NewE.

%% We want to place meta variables around all wave holes
%% These occur when there is a gap in the skeleton.
%% Andrew's paper suggests (though it does not explicitly say
%% that meta-variables should surround sinks and wave holes
%% I use a flag 0 or 1 to indicate whether or not the predicate is
%% traversing a wave front.
%% place_meta_vars A B _ C D:-
%%%%    printstdout A,
%%      printstdout B,
%%      printstdout C,
%%      printstdout D,
%%      fail.
place_meta_vars Term (leaf _ Pos _) Term Pos 0.
place_meta_vars Term (leaf _ Pos _) (app M [Term]) Pos 1.
place_meta_vars Term (sink _ Pos _) (app M [Term]) Pos _.
place_meta_vars (app F X) (node _ Pos FEtree EtreeL) Out Pos Flag:-
        !,
        ((Flag = 0, NFlag = 0); (Flag = 1, NFlag = 0)),
        place_meta_vars F FEtree NF (1 :: Pos) NFlag,
        mapcount EtreeL
          (Tree\ Term\ NewTerm\ N\ 
                (place_meta_vars Term Tree NewTerm (N :: Pos) Flag)) L NL 2.
place_meta_vars (app F L) Etree (app NF NL) TermPos Flag:-
        place_meta_vars F Etree NF (1 :: TermPos) 1,
        nth L Num Branch Rest,
	Num1 is Num + 1,
        place_meta_vars Branch Etree NB (Num1::TermPos) Flag,
        nth NL Num NB Rest.

place_meta_vars Term (node _ Pos FEtree AEtree) Term P 1:-
        not (P = Pos).


%%% revise induction

revise_induction (seqGoal (Hyps >>> WaveGoal) _Embedding) Scheme Subst Rule (seqGoal (H >>> OldGoal) _) Sc:-
	induction_schemes_list L,
	embeds_list Embedding WaveGoal NE _ _,
	mappred NE reverse_directions EmbeddingIn,
	repeat_ripple_in (seqGoal (Hyps >>> WaveGoal) [(embedding_context EmbeddingIn _)]) (seqGoal (Hyps >>> Goal) [(embedding_context NewEmb _)]) Rule,
	for_one NewEmb (E\ find_wave_fronts E WFPos _WHPos 0) _,
	memb (hyp (otype_of Var T) _) Hyps,
	subterm_of Goal Var WHPos,
	subterm_of Goal Subterm WFPos,
	subterm_of Subterm Var _,
	memb Scheme L, 
	(not (Scheme = Sc)),
	induction_scheme _  Scheme T Subst _ _ _,
	construct_subst Subterm Var Subst.
%	member_quant Goal Subgoals.
%%%	Worry about this later.
%%%	build_from_address NodeAddress GoalSequence.

local construct_subst osyn -> osyn -> subst -> o.
construct_subst Term1 Term2 (repl Term2 Term1).
construct_subst Term1 Term2 (dom C):-
		construct_subst Term1 Term2 (C _).

local find_wave_fronts etree -> (list int) -> (list int) -> int -> o.
find_wave_fronts (leaf _Dir Pos _) WFPos Pos ED:-
		 wave_front Pos ED WFPos.
find_wave_fronts (sink _ Pos _) WFPos Pos ED:-
		 wave_front Pos ED WFPos.
find_wave_fronts (node _ _ F A) WFPos WHPos ED:-
		 NED is ED + 1,
		 for_one A (E\ find_wave_fronts E WFPos WHPos NED) _.
		 
local wave_front (list int) -> int -> (list int) -> o.
wave_front Pos ED WFPos:-
		 length Pos Depth,
		 Depth > ED,
		 Diff is (Depth - ED),
		 drop_l Diff Pos WFPos.


is_quantifier_in Skel N N.
is_quantifier_in (app forall [Ty, (abs Prop Ty)]) Nin Nout:-
	N is (Nin + 1),
	pi v\ (is_quantifier_in (Prop v) N Nout).

member_quant X X.
member_quant X (Y ** Z):-
	member_quant X Y,
	member_quant X Z.
member_quant X (allGoal _ G):-
	pi z\ (member_quant X (G z)).

local norule rewrite_rule.
	
repeat_ripple_in (seqGoal (Hyps >>> Goal) [(embedding_context E1 _)]) ST R:-
	ripple_rewrite Hyps Rule (Goal @@ E1) (NewGoal @@ E2) Cond TermPos _ [] RDir,
	%% In even proofs even3 loses a wave front - this is measure reducing
	%% whether the wave front is inward or outward, so we want to avoid using this.
	not (R = Rule),
	trivial_condition Cond Hyps,
	embeds_list E2 NewGoal NE E1 E1p,
	measure_check inout NE E1p TermPos Embedding RDir,
	%% for_each Embedding not_zero,
	%% sinkability not needed - we're rippling towards the induction
	%% variable.
	 !,
	repeat_ripple_in (seqGoal (Hyps >>> NgewGoal) [(embedding_context Embedding inout)]) ST R.
repeat_ripple_in Goal Goal _.

%% reverse direction labels on an embedding.

local rd dir -> dir -> o.
rd inward outward.
rd outward inward.
rd inout inout.

reverse_directions (leaf A Pos _) (leaf B Pos _):-
		   rd A B.
reverse_directions (sink A Pos _) (sink B Pos _):-
		   rd A B.
reverse_directions (node A Pos E1 E2) (node B Pos E1P E2P):-
		   rd A B,
		   reverse_directions E1 E1P,
		   mappred E2 reverse_directions E2P.
reverse_directions (absnode A) (absnode B):-
		   pi x\ (reverse_directions (A x) (B x)).


%%  find_nearest_ind_meth

find_nearest_meth M Address Address:-
	get_method Address Meth, 
	Meth = M, !.
find_nearest_meth M Address Node:-
	parent_address Address NewAddress,
	find_nearest_meth M NewAddress Node.

find_previous_meth M Address Address:-
        retrieve_node Address Plan,
	get_method Address Meth, 
	Meth = M.
find_previous_meth M Address Node:-
	parent_address Address NewAddress,
	find_previous_meth M NewAddress Node.

parent_address (H::Ad) Ad.

%% Lemma speculation Critic

%% - Lemma Calculation

/*
compound_critic wave (wave_patch failed_rewrite Ad _Rule)
	(subplan_crit Ad
	(then_crit 
		(lemma_calculation OutLemma) 
	(subplan_crit Ad 
	   (continue_crit (m\ (then_meth (introduce_discovered_lemma OutLemma) 
			(pair_meth m (induction_top with_critics)))))))).
compound_critic wave (wave_patch failed_measure Ad _Rule)
	(subplan_crit Ad
	(then_crit 	
		(lemma_calculation OutLemma) 
	(subplan_crit Ad 
	   (continue_crit (m\ (then_meth (introduce_discovered_lemma OutLemma) 
			(pair_meth 
      (then_meth (formula_tester [1,0] evaluate (label_truth _ 0 0)) (induction_top with_critics)) 
       m
))))))).

atomic wave (introduce_discovered_lemma Lemma)
	(seqGoal (Hyps >>> Conc) E)
	true
	true
	(
         (seqGoal ([] >>> Lemma) []) 
         ** 
        (seqGoal (((hyp Lemma wrule)::Hyps) >>> Conc) E)
	)
	notacticyet.

atomic_critic wave (lemma_calculation OutLemma1)
	Address
	Agenda
	(get_goal Address (seqGoal (H >>> (app eq [LHS, RHS])) Context),
	  member (embedding_context Emb _) Context,
          map_split H (Hyp\ (sigma IH\ (Hyp = (hyp IH ind_hyp)))) IndHyps NewHyps,
	(
		%% Only rewrite once - otherwise things get hairy (see orevorev)
		%% But rewrite all skeletons

		(map_construct Emb (E\ In\ Out\ (sigma TermPos\ sigma Hyp\
		 memb (hyp Hyp ind_hyp) IndHyps,
		 rewrite_using_once Hyp In Out red 0 trueP (2::nil) TermPos,
		 in_embedding E TermPos)) LHS LHS1,
		%% don't bother if weak fertilisation will lead to a trivial truth.

		not (leave_to_weak_fertilisation LHS1 RHS NewHyps),
		Conc1 = (app eq [LHS1, RHS]));

		%% Only rewrite once - otherwise things get hairy (see orevorev)

		(map_construct Emb (E\ In\ Out\ sigma TermPos\ sigma Hyp\
		 memb (hyp Hyp ind_hyp) IndHyps,
		 rewrite_using_once Hyp In Out nored 0 trueP (3::nil) TermPos,
		 in_embedding E TermPos) RHS RHS1,
		not (leave_to_weak_fertilisation LHS RHS1 NewHyps),
		Conc1 = (app eq [LHS, RHS1]))), !,

		%% check result not ground - leave to weak fertilisation
		not (constant Conc1 _)
	)
	(generalise_lemma NewHyps Conc1 OutLemma,
	 check_for_redundant_quantifiers OutLemma OutLemma1,
	 not (member (hyp OutLemma1 wrule) H))
	nil
	Agenda.


local in_embedding etree -> (list int) -> o.
%% Base Cases
in_embedding (leaf _ TermPos _) TermPos:- !.
in_embedding (sink _ TermPos _) TermPos:- !.
in_embedding (node _ TermPos _ _) TermPos:- !.

in_embedding (node _ Ad E Etree) TermPos:-
	%% Only bother if TermPos might be below this positions somewhere.
	append X Ad TermPos,
	(in_embedding E TermPos;
         for_one Etree (E\ in_embedding E TermPos) _), !.
in_embedding (absnode E) TermPos:-
	pi x\ (in_embedding (E x) TermPos).


local leave_to_weak_fertilisation osyn -> osyn -> (list osyn) -> o.
%% New lemma is trivial
leave_to_weak_fertilisation X X _.
%% For multiple skeletons - new lemma is essentially original goal with some extra 
%% matching structure
%% Will need piecewise fertilisation

local check_for_redundant_quantifiers osyn -> osyn -> o.
check_for_redundant_quantifiers (app forall [Type, (abs (x\ F) Type)]) F1:-
	!, check_for_redundant_quantifiers F F1.
check_for_redundant_quantifiers (app forall [Type, (abs (x\ (F x)) Type)]) (app forall [Type, (abs (x\ (F1 x)) Type)]):-
	!, pi x\ (check_for_redundant_quantifiers (F x) (F1 x)).
check_for_redundant_quantifiers L L.

local generalise_lemma (list osyn) -> osyn -> osyn -> o.
local tmp_ann hyp_ann.

%% First quantify large subterms then variables.
generalise_lemma H (app eq [LHS, RHS]) (app forall [Type, (abs (x\ (OutLemma x)) Type)]):-
		%% As generalise lemma, generalise common subterms.
                [LHS, RHS] = [(NewA T), (NewB T)],
                not (headvar_osyn T), 
		not (obj_atom T),
                not (has_otype _ T _),
		not (member (hyp (otype_of T _) tmp_ann) H),
		pi x\ (not (subterm_of (NewA x) T _)), 
		pi x\ (not (subterm_of (NewB x) T _)), 
               	not ( NewA = (x\ _AA)),
                not ( NewB = (x\ _BB)),
                env_otype_inst_types T H Type,
	        env_otype_inst_types (NewA T) ((hyp (otype_of T Type) tmp_ann)::H) _, 
		pi X\ (generalise_lemma ((hyp (otype_of X Type) tmp_ann)::H) (app eq [NewA X, NewB X]) (OutLemma X)).
generalise_lemma H G (app forall [Type, (abs (x\ (OutLemma x)) Type)]):-
	G = (Term T),
	not (headvar_osyn T),
	obj_atom T,
	not (has_otype _ T _),
	not (member (hyp (otype_of T _) tmp_ann) H),
	pi x\ (not (subterm_of (Term x) T _)), !,
	not (Term = (x\ _)),
	member (hyp (otype_of T Type) _) H, !,
	pi X\ (generalise_lemma ((hyp (otype_of X Type) tmp_ann)::H) (Term X) (OutLemma X)).
generalise_lemma _ L L.

local map_construct (list B) -> (B -> A -> A -> o) -> A -> A -> o.
map_construct nil _ A A.
map_construct (H::T) P AIn AOut:-
	P H AIn ATmp,
	map_construct T P ATmp AOut. 

local map_split (list B) -> (B -> o) -> (list B) -> (list B) -> o.
map_split nil _ nil nil.
map_split (H::T) P (H::True) False:-
	P H, !,
	map_split T P True False.
map_split (H::T) P True (H::False):-
	map_split T P True False.

*/

%% Generalisation Critic - tested by qrevcorrect series in list_benchmarks

compound_critic wave (wave_patch (failed_sink Emb G) Ad _Rule)
	(subplan_crit Ad
	(then_crit 
		(generalisation_AI Emb G Lemma) 
 		(then_crit (roll_back_to_crit (induction_meth _ _ _) Address)
	(subplan_crit Address
		(continue_crit 
			(m\ (then_meth (introduce_gen Lemma)
			    (induction_top with_critics)))))))).

atomic_critic wave (generalisation_AI Emb NewGoal QLemma)
	Address
	Agenda
	(get_goal Address (seqGoal (Hyps >>> Conc) Em))
	(not (Conc = trueP),
	construct_generalisation (seqGoal (Hyps >>> Conc) Em) Emb NewGoal Lemma,
	 quantify_lemma Hyps Lemma QLemma)
	nil
	Agenda.

%% Method for introducing a generalisation 

atomic wave (introduce_gen Lemma)
	(seqGoal (Hyps >>> Conc) Context)
	true
	true
	(seqGoal (Hyps >>> Lemma) ((newgen Conc Lemma)::Context))
	notacticyet.

atomic wave (introduce_lemma Lemma)
	(seqGoal (Hyps >>> Conc) Emb)
	true
	true
	((seqGoal (Hyps >>> Lemma) []) ** (seqGoal (((hyp Lemma nha)::Hyps) >>> Conc) Emb))
	notacticyet.

%% Given a generalisationin quantify over the free variables.
quantify_lemma Hyps Lemma Lemma:-
	(not (member (hyp (otype_of X T) _) Hyps)).
quantify_lemma Hyps Lemma Out :-
	memb_and_rest (hyp (otype_of X T) _) Hyps NewH,
	subterm_of Lemma X _,
	forall_elim X T Lemma NewG,
	(not (subterm_of NewG X _)), !,
	quantify_lemma NewH NewG Out.
quantify_lemma Hyps Lemma Out :-
	memb_and_rest (hyp (otype_of X T) _) Hyps NewH,
	quantify_lemma NewH Lemma Out.

%% This is where the real work happends 

%% Walsh Critic
construct_generalisation (seqGoal (Hyps >>> _) _) Emb NewGoal (app forall [nat, (abs (n\ (Out n)) nat)]):-
	memb (hyp H1 ind_hyp) Hyps,
	pi x\ (iterate_wave_fronts x H1 NewGoal (Out x)).

%% Ireland Critic
%% Clause for equality goals
construct_generalisation (seqGoal (Hyps >>> _) [(embedding_context OldEs _)]) Emb _ GEN  :-
	memb (hyp H1 ind_hyp) Hyps,
	memb OldE OldEs,
	OldE = (node _ _ (leaf _ _ eq) _),
%	printstdout "a",
	unsinkable_flag 1 Emb Pos nil,
%	printstdout "b",
%	printstdout H1,
%	printstdout Pos,
	construct_gen_terms H1 _ _ GEN Pos Type 1.

%% Clause of not equality goals.
construct_generalisation (seqGoal (Hyps >>> _) [(embedding_context E _)]) Emb _ (app forall [Type, (abs (x\ (GEN x)) Type)]):-
	memb (hyp T1 ind_hyp) Hyps,
	memb OldE E,
	(not (OldE = (node _ _ (leaf _ _ eq) L))),
	unsinkable_flag 1 Emb Pos nil,
	(pi x\ (construct_gen_terms T1 _ x (GEN x) Pos Type 0)).

%% Integer argument indicates type of goal and, if equality, whether we are in the LHS or RHSconstruct

construct_gen_terms (app forall [Type, (abs (x\ (Term x)) Type)]) OT Var 
	(app forall [Type, (abs (x\ (Gen x)) Type)]) Pos Ty N:- !,
	pi x\ (construct_gen_terms (Term x) OT Var (Gen x) Pos Ty N).

%% Non-equality goals
construct_gen_terms SuperTerm _ Var Gen Pos Type 0:- !,

	%% Pos is position of unsinkable wave front
	%% Find a sub-term of this position of appropriate type
	subterm_of SuperTerm Term Pos,
	subterm_of Term C _,
	has_otype_ C Ty,
	(not (Ty = (arrow _ _))),

	%% Generatlise and then replace in goal
	gen_term Var Term SubGen Type,
	replace_at SuperTerm SubGen Gen Pos.

%% Force term to be generalisaied into first argument
construct_gen_terms (app eq [LHS, RHS]) _ _ (app forall [Type, (abs (x\ (app eq [(GENL x), (GENR x)])) Type)]) Pos Type 1:- !,
	(pi x\ 
	    (construct_gen_terms LHS _ x (GENL x) Pos Type 2,
	     construct_gen_terms RHS _ x (GENR x) Pos Type 3)).


%% 
%% EqTerm is the term on one side or the other of an equality
%% OT is the term on the other side of the equality
%% Var is a meta variable - a new sink term
%% Pos is the position of the unsinkable wavefront
%% Type is the type of ?Var
%% N is 2 or 3 to indicate which side of the equality we're on
construct_gen_terms EqTerm OT Var Gen Pos Type N:-
	%% Because we are in one branch of an equality we have to modify Pos
	%% the location of the unsinkable wave front.
	reverse Pos (N::RevPos),
	reverse RevPos SubPos, 
	!, 

	%% Find a sub-term of this position of appropriate type
	subterm_of EqTerm Term SubPos,
	subterm_of Term C _,
	has_otype_ C Ty,
	(headvar_osyn Ty; (not (Ty = (arrow _ _)))),

	gen_term Var Term SubGen Type,
	replace_at EqTerm SubGen Gen SubPos.
%% One side that isn't blocked

%% place the meta var round some subterm. - only first if application 
%% this is clearly a hack.
%% Probably want a "generalise deepest applications" heuristic.
construct_gen_terms (app F L) _ Var (app F GenL) _ Type _:-
        nth L N (app F1 L1) Rest,
	gen_term Var (app F1 L1) Gen Type,
	nth GenL N Gen Rest.
%% place a meta var at the top of the term
construct_gen_terms SuperTerm _ Var Gen _ Type _:-
	gen_term Var SuperTerm Gen Type.

gen_term Var Term (app F [Var]) Type:-
	constant Term Type, 
	!.
%% gen_term Var (app F L) (app F NewL) Type:-
%%	 nth L N (app F1 L1) Rest,
%%	 gen_term Var (app F1 L1) SubGen Type,
%%	 nth NewL N SubGen Rest.
gen_term Var Term (app F [Term, (app G [Var])]) Type.
	

unsinkable_flag 0 (leaf outward _ _) _ _.
unsinkable_flag X (leaf inward _ _) Pos Pos.

% Inwards wave front
unsinkable_flag X (node inward _ F E) Pos Pos:-
        % Check subterm
        mapcount E (Y\ H1\ H2\ N\ (unsinkable_flag 0 Y _ (N::PosIn))) _ _ 2,
        unsinkable_flag 0 F _ (1::Pos).

% Outward wave front
unsinkable_flag 1 (node outward _ F EL) Pos PosIn:-
        (unsinkable_flag 1 F Pos (1::PosIn);
        (nth EL N E Rest,
	N1 is N + 1,
        unsinkable_flag 1 E Pos (N1::PosIn))).

unsinkable_flag 0 (node outward _ F E) _ PosIn:-
        mapcount E (Y\ H1\ H2\ N\ (unsinkable_flag 0 Y _ (N::PosIn))) _ _ 2,
        unsinkable_flag 0 F _ (1::PosIn).


iterate_wave_fronts _ (wild_card _) T T.
iterate_wave_fronts _ T T T.
iterate_wave_fronts X Y (app F [Y]) (app (app fun_iter [X, F]) [Y]).
iterate_wave_fronts X Y (app F [Z]) (app (app fun_iter [X, (app fun_compose [F, H])]) [Y]):-
	iterate_wave_fronts X Y Z (app (app fun_iter [X, H]) [Y]).
iterate_wave_fronts N (app F X) (app G Y) (app FOut Out):-
	iterate_wave_fronts N F G FOut,
	mappred2 X (iterate_wave_fronts N) Y Out.
iterate_wave_fronts N (abs X T) (abs Y T) (abs Z T):-
	pi x\ (iterate_wave_fronts N (X x) (Y x) (Z x)).
	

compound_critic wave (wave_patch (failed_embed Rule) Ad _Rule)
        (subplan_crit Ad
        (then_crit 
                (previous_casesplit Rule) 
	(subplan_crit Ad
		(continue_crit 
	       (m\ (then_meth post_ripple (induction_top with_critics))))))).

atomic_critic wave (previous_casesplit Rule)
	      Ad
	      Agenda
	      (rewr Rule _ (app F _) _ C,
	       find_previous_meth (wave_case_split R2) Ad _,
	       rewr R2 _ (app F _) _ C2,
	   (C2 = (app neg [C]); C = (app neg [C2]);
	   (C2 = trueP, C = (app neq [A, B]));
	   (C = trueP, C2 = (app neq [A, B]))))
	   true
	   nil
	   Agenda.
		   

end
