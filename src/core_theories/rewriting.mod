/*

File: rewriting.mod
Author: Louise Dennis / James Brotherston
Description: Methods for Symbolic Evaluation.
Last Modified: 20th August 2002

*/

module rewriting.

accumulate embed.

local rewrite_ub osyn -> osyn -> osyn -> mkey -> polarity -> osyn -> o.
local rewrite_transitive osyn -> osyn -> osyn -> mkey -> polarity -> osyn -> o.
local tidy_lemma osyn -> osyn -> o.

% Apply a rewrite rule, taking care that the direction of the implication
% is compatible with the polarity of the expression being rewritten.
%
% Can always rewrite with equivalence-preserving rewrite rules, even
% when the "polarity" is equiv_only.
%
% This code is crude and should be improved to allow more external control
% (especially from symbolic evaluation) over what kinds of rewrite rules
% are allowed. We should have an additional category for "dangerous"
% rewrite rules which introduce meta-variables.

% JB: note also that the atomic rewriting methods can only deal with trivial
% side conditions on rewrites - that is to say, either the condition "trueP"
% or a condition which is already present in the hypotheses.


%%%%%%%%%%%
% ATOMIC METHODS
%%%%%%%%%%%

atomic rewriting trivial
	(seqGoal (H >>> G) Context)
	(memb (hyp H1 _) H,
        sym_eval_rewrites_list List,
        rewrite_with_rules List Rule H1 falseP Cond,
        trivial_condition Cond H)
        (replace_in_hyps H (hyp H1 Ann) ((hyp falseP Ann)::nil) HH,
	 log_rewrite_rule Context Rule)
	(seqGoal (HH >>> G) Context)
	notacticyet.

atomic rewriting rewrite_with_hyp
        (seqGoal (H >>> G) Context)
        (underquantifiers H G G1 imp_rewrite)
        true 
	(seqGoal (H >>> G1) Context)
        notacticyet.

local underquantifiers (list osyn) -> osyn -> osyn -> (list osyn -> osyn -> osyn -> o) -> o.


local imp_rewrite (list osyn) -> osyn -> osyn -> o.
imp_rewrite Hyps (app imp [Hyp, Conc]) Conc1 :-
	safe_rewrite Hyp red Hyp,
	beta_reduce Hyps Hyp HB,
	rewrite_using HB Conc Conc1 red 0 trueP,
	env_otype Conc1 Hyps _.

%% additional clause for use with critics.
underquantifiers Hyps G _ _:-
	headvar_osyn G, !, fail.
underquantifiers Hyps (app forall [Type, (abs Goal Type)]) (app forall [Type, (abs Goal2 Type)]) P:- !,
	pi (x\ (underquantifiers ((hyp (otype_of x Type) nha)::Hyps) (Goal x) (Goal2 x) P)).

underquantifiers Hyps (app exists [Type, (abs Goal Type)]) (app exists [Type, (abs Goal2 Type)]) P :- !,
	pi (x\ (underquantifiers ((hyp (otype_of x Type) nha)::Hyps) (Goal x) (Goal2 x) P)).

underquantifiers Hyps G G1 P:-
	P Hyps G G1.

atomic rewriting rewrite_with_hyp
        (seqGoal (H >>> G) Context)
        (memb_and_rest (hyp Hyp Ann) H Rest,
	 (not (Ann = ind_hyp)),
	 (Ann = new_rewrite; safe_rewrite Hyp red Hyp),
	 beta_reduce Rest Hyp HB,
         rewrite_using HB G G1 red 0 Cond,
	 trivial_condition Cond Rest,
	 env_otype G1 Rest _,
	 mappred Rest (X\ Y\ sigma H\ sigma A\ sigma HY\
		(X = (hyp H A),
		 not (H = (otype_of _ _)),
		 rewrite_using HB H HY red 0 CondA, 
		 trivial_condition CondA Rest,
		 Y = (hyp HY A), !); X = Y) NewHyps
	)
        true 
	(seqGoal (((hyp HB Ann)::NewHyps) >>> G1) Context)
        notacticyet.

atomic rewriting rewrite_with_transitive_hyp
        (seqGoal (H >>> G) Context)
        (memb_and_rest (hyp Hyp Ann) H Rest,
         rewrite_using_transitive Hyp G G1 red 0 Cond,
	 trivial_condition Cond Rest,
	 env_otype G1 Rest _,
	 mappred Rest (X\ Y\ sigma H\ sigma A\ sigma HY\
		(X = (hyp H A),
		 not (H = (otype_of _ _)),
		 rewrite_using_transitive Hyp H HY red 0 CondA, 
		 trivial_condition CondA Rest,
		 Y = (hyp HY A), !); X = Y) NewHyps
	)
        true 
	(seqGoal (((hyp Hyp Ann)::NewHyps) >>> G1) Context)
        notacticyet.

atomic rewriting (rewrite_with ListPredicate Rule)
        ( seqGoal (H >>> G) Context)
        (ListPredicate List,
	((((member (banned BList) Context), !, partition_rw BList List _ Rest);            Rest = List), 
	   !,
         (rewrite_with_rules Rest Rule G G1 Cond,
	 (not (contains_meta_var_term G1)),
	 (underquantifiers H G1 _ (Hyps\ GA\ GB\ (not (GA = falseP))),
         (trivial_condition Cond H,
	 (env_otype G1 H _))))))
                              % check the condition is in the hypotheses
        (log_rewrite_rule Context Rule)
        (seqGoal (H >>> G1) Context)
        notacticyet.

atomic rewriting (rewrite_with ListPredicate Rule)
        ( seqGoal (H >>> G) Context)
        (ListPredicate List,
	((((member (banned BList) Context), !, partition_rw BList List _ Rest);            Rest = List), 
	   !,
         (rewrite_with_rules Rest Rule G G1 Cond,
	 (contains_meta_var_term G1,
	 (underquantifiers H G1 _ (Hyps\ GA\ GB\ (not (GA = falseP))),
         (trivial_condition Cond H,
	 (env_otype G1 H _)))))))
                              % check the condition is in the hypotheses
        (log_rewrite_rule Context Rule)
        (seqGoal (H >>> G1) Context)
        notacticyet.

partition_rw [] L [] L.
partition_rw (H::T) List (H::B) C:-
	memb_and_rest H List Rest, !,
	partition_rw T Rest B C.
partition_rw (H::T) List B C:-
	partition_rw T List B C.

log_rewrite_rule Context Rule:-
	memb (unsure _ RRINFO) Context,
	member (rrstatus Rule Tree Pointer 1) RRINFO.
log_rewrite_rule Context Rule.

atomic rewriting (rewrite_case_split ListPredicate Rule)
        ( seqGoal (H >>> G) Context)
	(ListPredicate List,
	(((member (banned BList) Context), !, partition_rw BList List _ Rest);            
		   Rest = List), 
	   !,
         rewrite_with_rules Rest Rule G G1 Cond,
         (not (trivial_condition Cond H)),
	 env_otype G1 H _,
	 casesplit_analysis H G Rule Cases ListPredicate)
	(mapfun Cases (x\ (seqGoal (((hyp x nha)::H) >>> G)) Context) GoalList,
		list2goal GoalList OutGoals, 
	update_gb_context OutGoals NewOutGoals [])
	NewOutGoals
	notacticyet.
change_method_vars (rewrite_case_split L Rule) (rewrite_case_split L _):-!.


%% JB: specialised rewriting methods that deal only with lemmas / defns

atomic rewriting (deploy_lemma Lemma)
	(seqGoal (H >>> G) Context)
	(lemma_rewrites_list List,
	 rewrite_with_rules List Lemma G G1 Cond,
	 trivial_condition Cond H)
	true
        (seqGoal (H >>> G1) Context)
	notacticyet.

atomic rewriting (unfold_defn Defn)
	(seqGoal (H >>> G) Context)
	(defn_rewrites_list List,
	 rewrite_with_rules List Defn G G1 Cond,
	 trivial_condition Cond H)
	true
        (seqGoal (H >>> G1) Context)
	notacticyet.



%% This is to allow rules to be differently instantiated by each call
%% to rewrite_with, deploy_lemma and unfold_defn under a repeat_meth.
%%
%% It is assumed that the ListPredicate has been given.
change_method_vars (rewrite_with ListPredicate Rule) (rewrite_with ListPredicate _) :- !.
change_method_vars (deploy_lemma Lemma) (deploy_lemma _) :- !.
change_method_vars (unfold_defn Defn) (unfold_defn _) :- !.


%%%%%%%%%%%%
% COMPOUND METHODS
%%%%%%%%%%%%


compound rewriting sym_eval
(repeat_meth 
	(orelse_meth rewrite_with_hyp
	(orelse_meth 
			(rewrite_with sym_eval_rewrites_list (R:rewrite_rule))
	(orelse_meth (then_meth rewrite_with_transitive_hyp 
                          (formula_tester [1,0] evaluate (label_truth _ 0 0)))
	(orelse_meth (rewrite_case_split sym_eval_rewrites_list (R1:rewrite_rule))
	(orelse_meth  redundant

	(orelse_meth (then_meth (then_meth (then_meth (try_meth (repeat_meth all_i)) existential)
				(repeat_meth (rewrite_with sym_eval_rewrites_list (R:rewrite_rule))))
				trivials)

	%% See if some "normalising" by moving implications can occur
	(orelse_meth (then_meth
		(then_meth (try_meth (repeat_meth all_i)) imp_i)
		(then_meth (try_meth (repeat_meth (orelse_meth and_e or_e)))
			 (orelse_meth (rewrite_with sym_eval_rewrites_list (R:rewrite_rule))
			(then_meth (repeat_meth rewrite_with_hyp) 
                         (formula_tester [3,0] evaluate (label_truth _ 0 0))))))
	
	(orelse_meth and_e or_e)))))))))
	Address
	(print_path Address).

local print_path (list int) -> o.
print_path [].
print_path (H::T):-
	   get_method T nomethodyet, !,
	   print_path T.
print_path (H::T):-
	   get_method T (rewrite_with _ _), !, fail.
print_path (H::T):-
	   get_method T _, !.
print_path (H::T) :-
	   print_path T.


compound rewriting general_rewriting
        (repeat_meth 
             ( orelse_meth 
              ( rewrite_with general_rewrites_list R)
                redundant
             )
        
	 )
      Address
      ((Address=[];
	(Address=(H::T), 
         get_method T Meth, 
         (not (Meth = (rewrite_with _ _)))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Code for Preconditions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% rewriting with specified rules
%
% Try equivalences first.

rewrite_with_rules RL X Left Right Cond :-
	beta_reduce [] Left BLeft,
        congr (R\ P\ LHS\ RHS\ C\ 
               (memb R RL, 
               rewr R P LHS RHS C)) X positive_polarity BLeft Right Cond _ _.

% congr takes formula rewrites and closes over formulas

%  Note that this version will not instantiate a meta-var on its own
%  to lhs of rewrite.  

/* original version 
congr Rewr R P X Y Cond TermPos TermPos:- 
	(not (headvar_osyn X)),
        Rewr R P X Y Cond,
	(not (bad_for_synthesis R Y)),
	(not (X = Y)).

*/

local dummyrr rewrite_rule.
% regular rewriting
congr Rewr R P X Y Cond TermPos TermPos:- 
	(not (headvar_osyn X)),

%	copy_term [X] [CleanX],
%	count_vars X CleanX 0 N1 XList,
%	N is (N1 - 1),
%	((make_var_pairs N DBInfo,
%	modify_args CleanX Xdb DBInfo,
%	replace_fs Xdb X1 N1 PairList); (N < 0, DBInfo = [], PairList = [], X1 = X)),

        Rewr R P X Y Cond,

%	reinstantiate XList DBInfo PairList,


	env_otype Y [] Type,
	(not ((not (R = dummyrr)),
	      bad_for_synthesis R Y)).


% function type
%% Cond witness is a hack to prevent reduction abstractions in
%% Conditions.  Why is cond included in the x\ ? check with benchmarks.

congr Rewr R P (abs In Type) (abs Out Type) (Cond witness) TPI TPO:-
        pi ( x\ has_otype bound x Type => (
		(not ((In x) = x)),
		(congr Rewr R P (In x) (Out x) (Cond x) TPI TPO)
	)).

% application terms
%
% Rewrite one argument.
%
%
% Must tag each function argument with a polarity, e.g. imp/2 lends
% polarity -,+ to its arguments. The polarity of a subexpression of a
% term T is calculated by multiplying its polarities relative to all the
% subexpressions of T. But how about polarity of a (maybe ground)
% subterm s_k of a term with flexible head, (H s_1 ... s_n) (which is
% itself a subterm of an expression E)? It seems we need to either build
% a constraint which relates the polarity of s_k to the (currently
% unknown) polar character of H, i.e.  p(s_k, E) = p(H, E) * q(H,K),
% where q(F,k) specifies the polarity of the kth argument of F.
% What about curried functions? We could just forget about it and 
% check in the object-level proof. Hmmm... interesting.
%

% Polarity is explained in Santiago's thesis.  In general the idea
% is that you do forward reasoning in the hypotheses - negative polarity
% and backwards reasoning in the goal - positive polarity.  Implication
% and negations (~ X is treated as X => false) complicate this since the
% LHS of an implication can be moved into the hypotheses.  Not sure
% whether a special case is needed for rewriting function symbols - I've
% assumed not that they just carry the polarity of the surrounding context.


congr Rewr R Polarity (app F In) (app F Out) Cond TPI TPO:-
	polarise (app F In) PolarIn,
	nth PolarIn N A Rest,
	(not (headvar_osyn A)),
	N1 is N + 1,
	congr Rewr R Polarity A OutA Cond (N1::TPI) TPO,
	mappred Rest unpolarise OutRest,
	nth Out N OutA OutRest.

congr Rewr R Polarity (app FIn Arg) (app FOut Arg) Cond TPI TPO:-
	(not (headvar_osyn FIn)),
  congr Rewr R Polarity FIn FOut Cond (1::TPI) TPO.

congr Rewr R Polarity (polar_term XPolarity X) Xout Cond TPI TPO:-
	(not (headvar_osyn X)),
  multiply_polarities Polarity XPolarity NewPolarity,
  congr Rewr R NewPolarity X Xout Cond TPI TPO.



rewrite_with_rules_eval RL Left Right Cond :-
        congr_eval (P\ LHS\ RHS\ C\ sigma R\ sigma RHSA\
               (memb R RL, 
               rewr R P LHS RHS C
%%	       printstdout RHSA,
%%	       ((not (contains_meta_var_term RHSA), 
%%	        rewrite_with_rules_eval RL RHSA RHS C, !); 
%%		RHS = RHSA)
)) positive_polarity Left Right Cond.

% congr takes formula rewrites and closes over formulas

%  Note that this version will not instantiate a meta-var on its own
%  to lhs of rewrite.  

congr_eval Rewr P X Y1 Cond :- 
        Rewr P X Y Cond, !,
	(congr_eval Rewr P Y Y1 Cond; Y = Y1).

% function type
%% Cond witness is a hack to prevent reduction abstractions in
%% Conditions.  Why is cond included in the x\ ? check with benchmarks.

congr_eval Rewr P (abs In Type) (abs Out Type) (Cond witness):-
        pi ( x\ ((not ((In x) = x)),
		(congr_eval Rewr P (In x) (Out x) (Cond x))
	)).

congr_eval Rewr Polarity (app F In) (app Fout Out) Cond :-
	polarise (app F In) PolarIn,
	for_as_many (F::PolarIn) (A\ OutA\ (congr_eval Rewr Polarity A OutA Cond)) (Fout::OutP) 1,
	mappred OutP unpolarise Out.

congr_eval Rewr Polarity (polar_term XPolarity X) Xout Cond:-
  multiply_polarities Polarity XPolarity NewPolarity,
  congr_eval Rewr NewPolarity X Xout Cond.

%%  Splitting into two cases to handle problems caused by
%%  unification when a user enters rewrite rule.  The fix
%%  slows things down a lot and so is applied only to user rewrites.

rewr (user_rewrite RuleName) _Polarity LHS RHS Cond :-
     definition _ (user_rewrite  RuleName) CondA LHSA RHSA,
	/*  This terribly convoluted way of doing instantiation is to prevent 
	problems with instantiation of rewrite rules users have introduced at
	the command line */
	copy_term [CondA, LHSA, RHSA] [Cond, LHS, RHS].

rewr RuleName _P LHS RHS C:-
	definition _ RuleName C LHS RHS.

rewr (user_rewrite RuleName) _Polarity LHS RHS Cond :-
     lemma _ (user_rewrite RuleName) equiv CondA LHSA RHSA,
	copy_term [CondA, LHSA, RHSA] [Cond, LHS, RHS].
rewr RuleName _Polarity LHS RHS Cond :-
     lemma _ RuleName equiv Cond LHS RHS.

rewr (user_rewrite RuleName) positive_polarity LHS RHS Cond :-
     lemma _ (user_rewrite RuleName) rtol CondA LHSA RHSA,
	copy_term [CondA, LHSA, RHSA] [Cond, LHS, RHS].
rewr RuleName positive_polarity LHS RHS Cond :-
     lemma _ RuleName rtol Cond LHS RHS.

rewr (user_rewrite RuleName) negative_polarity LHS RHS Cond :-
     lemma _ (user_rewrite RuleName) ltor CondA LHSA RHSA,  
	copy_term [CondA, LHSA, RHSA] [Cond, LHS, RHS].
rewr RuleName negative_polarity LHS RHS Cond :-
     lemma _ RuleName ltor Cond LHS RHS.

rewr (user_rewrite RuleName) _Polarity LHS RHS Cond :-
     axiom _ (user_rewrite RuleName) equiv CondA LHSA RHSA,
	copy_term [CondA, LHSA, RHSA] [Cond, LHS, RHS].
rewr RuleName _Polarity LHS RHS Cond :-
     axiom _ RuleName equiv Cond LHS RHS.

rewr (user_rewrite RuleName) positive_polarity LHS RHS Cond :-
     axiom _ (user_rewrite RuleName) rtol CondA LHSA RHSA,
	copy_term [CondA, LHSA, RHSA] [Cond, LHS, RHS].
rewr RuleName positive_polarity LHS RHS Cond :-
     axiom _ RuleName rtol Cond LHS RHS.

rewr (user_rewrite RuleName) negative_polarity LHS RHS Cond :-
     axiom _ (user_rewrite RuleName) ltor CondA LHSA RHSA,  
	copy_term [CondA, LHSA, RHSA] [Cond, LHS, RHS].
rewr RuleName negative_polarity LHS RHS Cond :-
     axiom _ RuleName ltor Cond LHS RHS.


polarise (app F X) X:-
	headvar_osyn F, !.

polarise (app imp [L, R])
          [(polar_term negative_polarity L),
                  (polar_term positive_polarity R)] :- !.

polarise (app iff [L, R])
         [(polar_term equiv_only L),
                 (polar_term equiv_only R)] :- !.

polarise (app neg [X]) [(polar_term negative_polarity X)] :- !.

%% polarise (app _ [A, B]) [A, B] :- !.

polarise (app _ X) X.

unpolarise (polar_term _ X) X :- !.
unpolarise X X.

% Take a list of fun_type_poly terms and wrap them using the polar_term/2 
% functor together with their polarities, depending on the function.
% If function has an unusual polarity, use that, otherwise mark all
% arguments as +ve.

% Multiply polarities.

multiply_polarities equiv_only _ equiv_only:-!.

multiply_polarities positive_polarity positive_polarity positive_polarity:-!.

multiply_polarities positive_polarity negative_polarity negative_polarity:-!.

multiply_polarities negative_polarity positive_polarity negative_polarity:-!.

multiply_polarities negative_polarity negative_polarity positive_polarity:-!.


%%%
%% Trivial Conditions
%%%

trivial_condition trueP _:- !.
trivial_condition Cond H:-
	member (hyp Cond _) H, !.
trivial_condition (app eq [X, X]) _ :- !.
trivial_condition (app eq [X, Y]) H:-
	member (hyp (app eq [Y, X]) _) H, !.
trivial_condition (app neq [X, Y]) H:-
	member (hyp (app neq [Y, X]) _) H, !.
trivial_condition (app (abs K _) [X]) H:-
	member (hyp (K X) _) H, !.
trivial_condition Cond _:-
        sym_eval_rewrites_list List,
        rewrite_with_rules List Rule Cond trueP trueP.
trivial_condition (abs Cond _) H:-
	pi x\ (trivial_condition (Cond x) H), !.



bad_for_synthesis beta_reduction Y:-
	headvar_osyn Y.
bad_for_synthesis beta_reduction (app X _):-
	headvar_osyn X.
bad_for_synthesis beta_idty Y:-
	headvar_osyn Y.

% use eq (with some universal quantification) to rewrite
%  ---- should check object typing here.

rewrite_ub (app forall [T, (abs F T)]) A B Mkey _ Cond:- 
	not (contains_meta_var_term A),
	!, rewrite_ub (F _T) A B Mkey _ Cond. 
rewrite_ub Hyp Hyp trueP _ _ trueP.
rewrite_ub (app neg [Hyp]) Hyp falseP _ _ trueP.
rewrite_ub Hyp (app neg [Hyp]) falseP _ _ trueP.
rewrite_ub (app eq [A, B]) A B red _ trueP:-
	not (constant A _).
rewrite_ub (app eq [A, B]) B A nored _ trueP:-
	not (constant B _).
% rewrite_ub (app imp [A, B]) X Y MKey Pol A:-
% 	rewrite_ub B X Y MKey Pol trueP.


rewrite_transitive Hyp (app F [C, D]) Out MKey positive_polarity trueP:-
        tidy_lemma Hyp (app F [L, R]),
        lemma _ _ _ trueP (app transitive [F]) trueP,
        ((C = L, Out = (app F [R, D]));
         (D = R, Out = (app F [C, L]))).
rewrite_transitive Hyp (app F [C, D]) Out MKey negative_polarity trueP:-
        tidy_lemma Hyp (app F [L, R]),
        lemma _ _ _ trueP (app transitive [F]) trueP,
        ((C = R, Out = (app F [L, D]));
         (D = L, Out = (app F [C, R]))).

local rewrite_ub_eval osyn -> osyn -> osyn -> mkey -> polarity -> osyn -> o.
rewrite_ub_eval (app forall [T, (abs F T)]) A B Mkey _ Cond:- 
	not (contains_meta_var_term A),
	!, rewrite_ub_eval (F _T) A B Mkey _ Cond. 
rewrite_ub_eval Hyp Hyp trueP _ _ trueP.
rewrite_ub_eval (app neg [Hyp]) Hyp falseP _ _ trueP.
rewrite_ub_eval Hyp (app neg [Hyp]) falseP _ _ trueP.
rewrite_ub_eval (app eq [A, B]) A B red _ trueP.
rewrite_ub_eval (app eq [A, B]) B A nored _ trueP.


% Could exploit polarity to our advantage here to allow rewriting with 
% IHs which are implications.

%% LD.  Modifying this to handle transitive predicates.  Notes here taken
%% from clam comments by Ian Green (I think).
%% For a function symbol - for which transitivity holds, we can
%% perform the following transformations on sequents:
%% 1. L~R |- X~S(R) into L~R |- X~S(L) if R occurs positive in S, or
%% 2. L~R |- S(L)~X into L~R |- S(R)~X if L occurs positive in S, or
%% 3. L~R |- X~S(L) into L~R |- X~S(R) if L occurs negative in S, or
%% 4. L~R |- S(R)~X into L~R |- S(L)~X if R occurs negative in S.

%% LD. I disagree with the above (though it may hold for implication)
%% - see below.  Basically I can't see how its true unless S is known
%% to be monotonic wrt. ~

%%
%% where the wave fronts must be: ``S({R})'' etc.
%% These can be reprased as:
%% 
%% 1. substitute R by L in rhs when R occurs positive, or
%% 2. substitute L by R in lhs when L occurs positive, or
%% 3. substitute L by R in rhs when L occurs negative, or
%% 4. substitute R by L in lhs when R occurs negative
%% 
%% If ~ is also symmetrical, we can drop the requirements on polarity.
%% The method below implements 1-2 in one method. It knows about
%% a set of function symbols which are transitive. It then always
%% does a fertilization replacing R by L, but it can assign L and
%% R to either lhs and rhs or vice versa, so we get the symmetry
%% we want.

%% I've modified this slightly (since I started worrying about
%% monotonic S etc. and we have polarity for -> and = handled
%% in our congr predicate ) so
%% 1.  L~R |- S(X~R) into L~R |- S(X~L) if R occurs +ve
%% 2.  L~R |- S(L~X) into  L~R |- S(R~X) if L occurs +ve
%% 3.  L~R |- S(X~L) into L~R |- S(X~R) if L occurs -ve
%% 4.  L~R |- S(R~X) into L~R |- S(L~X) if L occurs -ve


%% rewrite_using (app forall [T, (abs F T)]) A B Mkey FertFlag Cond:- 
%%	!, rewrite_using (F _T) A B Mkey FertFlag Cond. 
rewrite_using Hyp F G Mkey FertFlag Cond:-
	not (contains_meta_var_term F),
	tidy_lemma Hyp H,	
	% transform \x.x A to A
	beta_reduce [] F FB,
	(FertFlag = 0; (FertFlag = 2; (not (not (embeds _ H F))))),
        (((FertFlag = 0; FertFlag = 1), congr (r\ pol\ in\ out\ cond\ (rewrite_ub H in out Mkey pol CondA)) _Rule positive_polarity FB F1 _ _ _);
        (((FertFlag = 2; (constant FB _)), congr (r\ pol\ in\ out\ cond\ (rewrite_ub_eval H in out Mkey pol CondA)) _Rule positive_polarity FB F1 _ _ _))),
	%% NB. Hyp will be instantiated at this point
	((safe_rewrite H Mkey H, not (F1 = FB),
	rewrite_using H F1 G Mkey FertFlag CondB, merge_conds CondA CondB Cond, !); (G = F1, CondA = Cond)).


rewrite_using_transitive (app forall [T, (abs F T)]) A B Mkey FertFlag Cond:- 
	!, rewrite_using_transitive (F _T) A B Mkey FertFlag Cond. 
rewrite_using_transitive Hyp F G Mkey FertFlag Cond:-
	tidy_lemma Hyp H,	
	% transform \x.x A to A
	(FertFlag = 0; (not (not (embeds _ H F)))),
        congr (r\ pol\ in\ out\ cond\ (rewrite_transitive H in out Mkey pol CondA)) _Rule positive_polarity F F1 _ _ _,
	((safe_rewrite H Mkey H, rewrite_using_transitive H F1 G Mkey FertFlag CondB, merge_conds CondA CondB Cond!); (G = F1, CondA = Cond)).


rewrite_using_once (app forall [T, (abs F T)]) A B Mkey FertFlag Cond TPI TPO:- 
	!, rewrite_using_once (F _T) A B Mkey FertFlag Cond TPI TPO. 
rewrite_using_once Hyp F G Mkey FertFlag Cond TPI TPO:-
	tidy_lemma Hyp H,	
	% transform \x.x A to A
	(FertFlag = 0; (not (not (embeds _ H F)))),
        congr (r\ pol\ in\ out\ cond\ (rewrite_ub H in out Mkey pol Cond)) _Rule positive_polarity F G _ TPI TPO.

local merge_conds osyn -> osyn -> osyn -> o.
merge_conds trueP X X:- !.
merge_conds X trueP X:- !.
merge_conds X Y (app and [X, Y]).
	

tidy_lemma X X:-
	headvar_osyn X, !.
tidy_lemma X X:-
	obj_atom X.
tidy_lemma (wild_card T) (wild_card T).
tidy_lemma (app F [A]) B:-
	not (headvar_osyn F),
	F = (abs (x\x) _),
	tidy_lemma A B.
tidy_lemma (app F A) (app G B):-
	tidy_lemma F G,
	mappred A tidy_lemma B.
tidy_lemma (abs F T) (abs G T):-
	pi (x\ (tidy_lemma (F x) (G x))).


%% JB: function to convert a goal to a (directed) lemma

goal_to_lemma ReasonType Goal Theory (user_rewrite Name) Dir Cond Lhs Rhs:-
   top_goal Theory Goal Hyps Conc,
   print "Theory found: ", pprint_name Theory,
   term_to_string Goal GoalName, 
   term_to_string ReasonType DirName,
   Name is (GoalName ^ "_" ^ DirName),
   print "Lemma name:   ", pprint_string Name,
   ((ReasonType = bwd, Dir = rtol) ; (ReasonType = fwd, Dir = ltor)), !,
   print "Direction:    ", pprint_name Dir,
   convert_hyps_to_cond Hyps Cond, !,
   print "Conditions:   ", pprint_name Cond,
   convert_conc_to_rewrite Dir Conc Lhs Rhs, !,
   pprint_string "Lemma:",
   pprint_term Lhs, print " ==> ", pprint_term Rhs.
   

local convert_hyps_to_cond (list osyn) -> osyn -> o.

convert_hyps_to_cond [] trueP:- !.
convert_hyps_to_cond [Hyp] Hyp:- !.
convert_hyps_to_cond (Hyp::RestHyps) (app and [Hyp, RestCond]):-
  convert_hyps_to_cond RestHyps RestCond.


local convert_conc_to_rewrite direction -> osyn -> osyn -> osyn -> o.

convert_conc_to_rewrite rtol (app imp [A,B]) B A.
convert_conc_to_rewrite ltor (app imp [A,B]) A B.
convert_conc_to_rewrite rtol (app eq [A,B]) B A.
convert_conc_to_rewrite ltor (app eq [A,B]) A B.
convert_conc_to_rewrite rtol (app iff [A,B]) B A.
convert_conc_to_rewrite ltor (app iff [A,B]) A B.
convert_conc_to_rewrite Dir (app forall [Type, (abs (X\ (F X)) Type)]) L R:- 
   (sigma Z\ (convert_conc_to_rewrite Dir (F Z) L R)).
convert_conc_to_rewrite Dir (app exists [Type, (abs (X\ (F X)) Type)]) L R:-
   (sigma Z\ (convert_conc_to_rewrite Dir (F Z) L R)).
convert_conc_to_rewrite Dir Other Other trueP.


local apply_casesplit (list osyn) -> osyn -> rewrite_rule -> (list osyn) -> (list rewrite_rule -> o) -> o.

local complete_cases osyn -> (list osyn) -> o.


%% wave_casesplit_method intended to be invoked by a critic

casesplit_analysis Hyps Term Rule Cases ListPred:-
        findall (x\ apply_casesplit Hyps Term Rule x ListPred) CaseList,
        memb Cases CaseList.

apply_casesplit Hyps Term Rule Cases ListPred:-
		ListPred L,
        %% Rule is instantiated as we come in, but just in case
        %% Check rule actual rewrites term somewhere
        rewrite_with_rules L Rule Term _ Cond,
        complete_cases Cond Cases,
        for_each Cases (x\ (not (member (hyp x _) Hyps))).

complete_cases S _:-
	       subterm_of S witness _, !, fail.
complete_cases (app (abs F _) [X]) Out:-
	complete_cases (F X) Out.
complete_cases (app neg [X]) [(app neg [X]), X]:-!.
complete_cases (app neq [X, Y]) [(app neq [X, Y]), (app eq [X, Y])]:- !, not (X = Y).
complete_cases (app eq [X, Y]) [(app eq [X, Y]), (app neq [X, Y])]:- !, not (X = Y).
complete_cases X [X, (app neg [X])].

local for_as_many (list X) -> (X -> Y -> o) -> (list Y) -> int -> o.
for_as_many nil P nil 0:- !.
for_as_many (X::L) P (Y::K) 1:- P X Y, !, for_as_many L P K _.
for_as_many (X::L) P (X::K) N:- for_as_many L P K N, !.


local safe_rewrite osyn -> mkey -> osyn -> o.
safe_rewrite trueP _ _:- !, fail.
safe_rewrite (app forall [T, (abs F T)]) Mkey Hyp:- !,
	pi x\ (safe_rewrite (F x) Mkey Hyp).
safe_rewrite (app eq [A, B]) red Rule :-
	not (rewrite_using_once Rule B _ red 0 _ _ _, !).
safe_rewrite (app eq [A, B]) nored Rule :-
	not (rewrite_using_once Rule A _ nored 0 _ _ _, !).
safe_rewrite Term _ _:-
	not (Term = (app eq [_, _])), !.

beta_reduce Hyps A A:-
	    headvar_osyn A, !.
beta_reduce Hyps A A:-
	    obj_atom A, !.
beta_reduce Hyps (app F Args) (app F NewArgs):-
	    headvar_osyn F,
	    !,  mappred Args (beta_reduce Hyps) NewArgs.
beta_reduce Hyps (app (abs (X\ (F X)) Type) [H]) Out:-
	    !, beta_reduce Hyps (F H) Out.
beta_reduce Hyps (app (abs (X\ (F X)) Type) (H::Args)) Out:-
	    !, env_otype H Hyps Type,
	    beta_reduce Hyps (app (F H) Args) Out.
beta_reduce Hyps (app F Args) (app NewF NewArgs):-
	    !,  mappred (F::Args) (beta_reduce Hyps) (NewF::NewArgs).
beta_reduce Hyps (abs (X\ (F X)) Type) (abs (X\ (NewF X)) Type):-
	    !,  (pi x\ (has_otype embed x Type => beta_reduce Hyps (F x) (NewF x))).


%% Find number of free (app) vars and set up permutation key lists.
make_var_pairs 0 [(syn_pair (db 0) CL F)].
make_var_pairs N ((syn_pair (db N) CL PL)::L):-
	N > 0,
	N1 is (N - 1),
	make_var_pairs N1 L.

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


replace_fs X X 0 [].
replace_fs Xin XOut N1 ([(db N), F]::L):-
	N1 > 0,
	N is (N1 - 1),
	replace_with Xin (db N) F Xint,		
	replace_fs Xint XOut N L, !.

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
recomb [] ArgList PL (app F Args) F:-
	reverse ArgList RArgList,
	permutation PL RArgList Args.

%%% Warning really need a flag or something to distinguish special case.
%% recomb CL AL PL F F:-
%%        for_each CL (X\ (X = 1)),
%%        for_each PL (X\ (X = 1)), !.
recomb (1::N) List PL (abs (X\ (F X)) Type) Inst :-
	pi (x\ (has_otype embed x Type => (recomb N (x::List) PL (F x) Inst))).
recomb (0::N) List PL (abs (X\ (F X)) Type) Inst:-
	pi (x\ (has_otype embed x Type => (recomb N List PL (F x)) Inst)).

reinstantiate [] _ _.
reinstantiate ([F, (db N)]::L) DBInfo DBInsts:-
	memb ([(db N), G]) DBInsts,
	memb (syn_pair (db N) CL PL) DBInfo,
	((for_each CL (X\ (X = 1)),
          for_each PL (X\ (X = 1)),
	  G = F);
	  recomb CL [] PL F G),
	reinstantiate L DBInfo DBInsts, !.

end
