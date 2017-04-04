/* 

File: induction.mod
Author: Louise Dennis / James Brotherston
Description: Induction Methods
Last Modified: 20th August 2002 

*/

module induction.

accumulate schemes, generalise, pwf.

local   sink_match      osyn -> osyn -> (list osyn) -> o.

local apply_suggestion (list subst) -> int -> int -> scheme -> goal -> scheme -> goal -> o.
local merge_scheme scheme -> scheme -> scheme -> o.
local count_quantifiers osyn -> int -> o.
local remove_previous_ind_hyps (list osyn) -> (list osyn) -> o.


lemma induction triv_abs equiv
	trueP
	(app (abs (X\ X) _) [W])
	W.

compound induction trivials
	(complete_meth (repeat_meth (orelse_meth (orelse_meth all_i trivial) equality_condition)))
	_
	true.

atomic induction equality_condition
	(seqGoal (H >>> (app eq [A, B])) Context)
	(rewrite_with_rules [idty, triv_abs] Rule (app eq [A, B]) trueP Cond,		 
	trivial_condition Cond H)
	true
	(seqGoal ( H >>> trueP) Context)
	notacticyet.

atomic induction truegoalmeth
	(seqGoal (H >>> trueP) Context)
	true
	true
	(seqGoal (H >>> trueP) Context)
	notacticyet.
atomic induction fertilisation_strong
	( seqGoal (H >>> G) Context)
	(memb (hyp H1 ind_hyp) H,
	 sink_match_ H1 G G2 H)  %jndw 2/12: modulo matching of sinks
	 (filter Context NewContext (H1\ (sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	 beta_reduce H G2 Gout,
	 mappred H (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce Hyps X Z;
		  Z = X)),
		 B = (hyp Z T))) NewHyps)
	(seqGoal (NewHyps >>> Gout) NewContext)
	notacticyet.

%
% Weak fertilisation. Attempts to use a hypothesis L=R as a rewrite
% rule left-to-right or right-to-left, deleting the used hypothesis
% from the hypothesis list. Alternatively, if a copy of the entire hypothesis
% appears in the goal, it is replaced by trueP, and the used hypothesis is
% retained.
%

% no case for sinks yet
atomic induction fertilisation_weak
        ( seqGoal (H >>> (app eq [LHS, RHS]) ) Context)
        ( memb_and_rest (hyp Hyp ind_hyp) H NewHyps,
          (rewrite_using Hyp LHS LHS1 red 0 Cond, RHS1 = RHS;
           rewrite_using Hyp RHS RHS1 nored 0 Cond, LHS1 = LHS),
	  trivial_condition Cond NewHyps
	)
	 (filter Context NewContext (H1\ (sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	 beta_reduce H (app eq [LHS1, RHS1]) Goal,
	 %% changed H to NewHyps in mappred
	 mappred NewHyps (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce H X Z);
		  Z = X),
		 B = (hyp Z T))) NH
	%% replace any introduced meta-variables
%%	replace_meta_vars Goal (app eq [LHS, RHS]) H
	)
	( seqGoal ( NH >>> Goal ) NewContext)
        notacticyet.

local replace_meta_vars osyn -> osyn -> list osyn -> o.
local dummy_check osyn.
replace_meta_vars Goal OldTerm _:-
	(not (contains_meta_var_term Goal); contains_meta_var_term OldTerm).
replace_meta_vars Goal OldTerm H:-
	not (contains_meta_var_term OldTerm),
	subterm_of_mv Goal X,
	headvar_osyn X,
	memb (hyp X nha) H.
	
local subterm_of_mv osyn -> osyn -> o.
subterm_of_mv T T.
subterm_of_mv (app X _) Y:- subterm_of_mv X Y.
subterm_of_mv (app _ Y) X:- memb ST Y,
		            subterm_of_mv ST X.
subterm_of_mv (abs X _) T :- pi u\ (subterm_of_mv (X u) T).

atomic induction fertilisation_weak
        ( seqGoal (H >>> G ) Context)
        ( memb_and_rest (hyp Hyp ind_hyp) H NewHyps,
          (rewrite_using Hyp G G1 _ 1 Cond;
           rewrite_using_transitive Hyp G G1 _ 1 Cond),
	  trivial_condition Cond NewHyps
	)
	 (filter Context NewContext (H1\ (sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	 beta_reduce H G1 G2,
	 mappred NewHyps (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T), 
		 ((T = new_rewrite, beta_reduce H X Z;
		  Z = X)),
		 B = (hyp Z T))) NH)
	( seqGoal ( NH >>> G2 ) NewContext)
        notacticyet.


atomic induction (induction_meth _I Scheme Subst)
    (seqGoal (H >>> G) Context) 
%% Louise 11th Jan added H to all_ripple_analysis - attempt to induct on skolem
%% constants - think this is a hack.... maybe.

%% Count the number of quantifers (i.e. potential number of variables to be used to 
%% induct upon and produce a list of possible induction schemes.
    ( 	% pprint_string "Counting quantifiers",
	% Remove ind_hyp annotations -- needed to prevent unwanted embeddings
	beta_reduce H G BG,
	remove_previous_ind_hyps H H1,
	count_quantifiers BG Max,
	pprint_string "Ripple analysis",
	all_ripple_analysis Max H1 BG Suggestion,
	pprint_string "Applying suggestion",
	printstdout Suggestion,
	% This is for synthesis proofs
%% remove_existentials and insert_witness were experiments in making
%% sythesis work more effecitively
%%	remove_existentials G GWit nil,
	apply_suggestion Suggestion 0 0 no_scheme (seqGoal (H1 >>> BG) Context) Scheme Subgoals
%%	insert_witness_goal Subgoals SubgoalsWit Witness
%%	break_up_under_witness_goal Subgoals SubgoalsEx
	)
    (update_gb_context Subgoals NewSubgoals [])
    NewSubgoals
    notacticyet.
change_method_vars (induction_meth _ _ _) (induction_meth _ _ _).

remove_previous_ind_hyps [] [].
remove_previous_ind_hyps ((hyp H ind_hyp)::T) ((hyp H nha)::T1):-
	!, remove_previous_ind_hyps T T1.
remove_previous_ind_hyps (H::T) (H::T1):-
	!, remove_previous_ind_hyps T T1.
 

% suggestion may involve more than one variable.

apply_suggestion Suggestion N1 _ SchemeIn SGIn SchemeIn SGIn:-
	not (
	nth Suggestion N Subst _,
		not (Subst = empty), 
		N > N1).
apply_suggestion Suggestion N1 C SI G SO SGO:-
	nth Suggestion N Subst _,
	not (Subst = empty), 
	% what is happening here is I have a list of induciton schemes to be applied to 
	% each universally quantified variable.  These appear in the same order as the variables.
	% nth will pick (the meaningul (i.e. not empty ones of) these out in order, returning N 
        % which is the place in the list they appear.  N is then used to apply them to the correct
	% variable in the goal.  In order to force them all to be chosen I pass N as an argument
        % to the recursive case and require that the next one picked is further into the list
	% i.e. N > N1 below!
	N > N1, !,

	% My next problem is that once I've applied a scheme I have one less universal quantifier 
	% in the goal - so N is out of sync with the quantifiers.  So I've introduced C which
	% counts the number of times I've applied the scheme and take this away from N in 
	% order to continue to identify the correct quantifier.
	N2 is N - C,
	applicable_induction_scheme Scheme Subst G N2 Subgoals,
	merge_scheme SI Scheme Schemes,
	C1 is C + 1,
	
	% I pass Subgoals as the new goal and applicable_induction_scheme works sensibly on compound
	% goals.
	apply_suggestion Suggestion N C1 Schemes Subgoals SO SGO.

merge_scheme no_scheme Scheme Scheme:- !.
merge_scheme S1 S2 (and_scheme S1 S2).

count_quantifiers (app forall [Type, (abs (x\ (F x)) Type)]) N:-
	!, pi x\ (count_quantifiers (F x) N1),
	N is N1 + 1.
count_quantifiers P 0.

%jndw 2/12
% doesn't yet check that the sinks are equalised '
% Louise: Does now (I think!)

%% Louise:  Only used in strong fertilisation

sink_match X X _.
sink_match X Y H:-
	   headvar_osyn Y,
	   member (hyp (otype_of X _) witness_term) H,
	   Y = witness.
sink_match X Y _:-
	headvar_osyn X, !, fail.
sink_match (app forall [Type, (abs X Type)]) (app forall [Type, (abs Y Type)]) H:- 
    sink_match (X Z) (Y Z) H.
sink_match (app forall [Type, (abs X Type)]) Y H:- 
    sink_match (X Z) Y H.
sink_match (app exists [Type, (abs X Type)]) Y H:- 
    sink_match (X witness) Y H.

sink_match (abs X Type) (abs Y Type) H:-
    pi z\ (sink_match (X z) (Y z) H).
sink_match (app F A) (app G B) H:-
    sink_match F G H,
    mappred A (X\ Y\ (sink_match X Y H)) B.
%% Remaining machinery needed because the sink might be \x.x 
sink_match (app F A) B H:-
    headvar_osyn F,
    nth A N A1 _,
    sink_match A1 B H.
sink_match A (app G [B]) H:-
    headvar_osyn G,
    (not (headvar_osyn B)),
    sink_match A B H.

sink_match_ _ Y _ _:- headvar_osyn Y, !, fail.
sink_match_ X Y trueP H:- 
	sink_match X Y H, 
	!.
sink_match_ L (app F M) (app F Mout) H:-
	nth M N MIn MRest,
	sink_match_ L MIn Out H,
	nth Mout N Out MRest,
	%% Check the new expressions type checks - to prevent random truePs turning up.
	has_otype_ (app F Mout) _, !.

compound induction (induction_top IndType) (complete_meth
		(repeat_meth
		(orelse_meth trivials
		(orelse_meth allFi
	 	(orelse_meth taut
            	(orelse_meth (cond_meth contains_any_meta_var_goal fail_meth sym_eval)
		(orelse_meth (then_meth existential (try_meth sym_eval))
		(orelse_meth (repeat_meth generalisation_compound)
                         (ind_strat IndType)
	))))))))
	_
	true :- not (IndType = sym_eval_crit; IndType = error_loc).

/*
compound induction (step_case normal_ind)
        (cut_meth
	(then_meth
           (then_meth (try_meth (repeat_meth all_i)) set_up_ripple)

	   (then_meth 
             (orelse_meth
	       (then_meth
	          (then_meth 
                     (repeat_meth (wave_method outward R))
	             (try_meth (unblock UR))
                  )
	         (orelse_meth 
                   (repeat_meth fertilisation_strong)
		   (then_meth	
		      (try_meth (then_meth
                              (repeat_meth (wave_method inout R1))
			      (try_meth (unblock UR1))
		       ))
		      (try_meth fertilise)
		  )
	         )
	       )
	
	
	      (then_meth
	         (then_meth	
	           (repeat_meth (wave_method inout R1))
                   (try_meth (unblock UR1))
	         )
	         fertilise
                )
             )
	

%%	    (then_meth 
                (then_meth post_ripple (try_meth (repeat_meth generalisation_compound))) 
%%                (then_meth
%%		    (then_meth (try_meth sym_eval) (try_meth fertilise))
%%		    (try_meth (repeat_meth all_e))
%%                )
%%            )
           )
        ))
	_
	true.
*/
                

compound induction ripple_coerce_vars (then_meth coerce_vars check_embedding) _ true.

atomic induction check_embedding
       (seqGoal (H >>> G) C)
       (memb_and_rest (embedding_context E Dir) C NewC,
       	beta_reduce H G BG,
	mappred E modify_embedding NewE,
	mappred H (A\ B\ sigma X\ sigma Z\ sigma T\ (
		 A = (hyp X T),
		 (((T = new_rewrite; T = ind_hyp), beta_reduce H X Z); X = Z),
		 B = (hyp Z T))) NewH,
        for_each NewE (X\ (set_epos X BG)))
	true
	(seqGoal (NewH >>> BG) ((embedding_context NewE Dir)::NewC))
	notacticyet.


control_rule_for induction coerce_vars_control G List NewList:-
	((contains_meta_var_goal G, !, 
		reject [fertilise, fertilisation_strong, ripple_strat _] List NewList1,
		prefer [ripple_coerce_vars] NewList1 NewList2,
		replace (wave_method outward R) (then_meth (wave_method outward R) (cond_meth contains_meta_var_goal id_meth ripple_coerce_vars)) NewList2 NewList3,
		replace (wave_method inout R) (then_meth (wave_method inout R) (cond_meth contains_meta_var_goal id_meth ripple_coerce_vars)) NewList3 NewList); (
	reject [ripple_coerce_vars, (ripple_synthesis_strat _)] List NewList)).

control_rule_for induction (outward_ripple IndType) (seqGoal G L) 
                                                         List NewList:- 
	member (embedding_context _ outward) L,
	prefer [fertilisation_strong,
		(wave_method outward R), %% (unblock UR1), 
%%                fertilisation_strong, 
		(wave_method inout R1)] List NewList1,
	((contains_meta_var_goal (seqGoal G L), IndType = with_critics, !, NewList = NewList1);
	ripple_operate IndType NewList1 NewList).

control_rule_for induction (inward_ripple IndType) 
                           (seqGoal G L) List NewList:-
	member (embedding_context _ inout) L,
	prefer [fertilisation_strong, %% (unblock UR1), 
		fertilise, 
                (wave_method inout R1)] List NewList1,
	((contains_meta_var_goal (seqGoal G L), IndType = with_critics, !, NewList = NewList1);
	ripple_operate IndType NewList1 NewList).

ripple_operate normal_ind List List.
ripple_operate with_critics List NewList:-
	replace (wave_method inout R1) (patch_meth (wave_method inout T1) wave_critic_strat) List NewList.

compound induction (ripple_strat Type)
	(repeat_meth (strat_meth
        [coerce_vars_control, (outward_ripple Type), (inward_ripple Type), after_fertilisation]
	[fertilisation_strong, %% (unblock UR1), 
	fertilise, 
         (wave_method outward R), (wave_method inout R2), ripple_coerce_vars]))
	_
	true.

compound induction (start_ripple_strat Type)
	(repeat_meth (strat_meth
        [ripple_set_up Type]
	[all_i, exists_e, existential, set_up_ripple]))
%	[set_up_ripple]))
        _
	true.

control_rule_for induction after_fertilisation (seqGoal G L) List NewList:-
        not (member (embedding_context _ _) L),
	reject [(wave_method outward R), %% (unblock UR1), 
		(wave_method inout T1), fertilise] List NewList.


compound induction (ripple_synthesis_strat Type)
	 (then_meth
		(ripple_strat Type)
		(cond_meth (G\ (not (contains_meta_var_goal G)))
			   (try_meth (ripple_strat Type))
			   fail_meth))
	_
	true.

control_rule_for induction (ripple_set_up Type) _ List NewList:-
	not (Type = lim_thm),
	prefer [all_i, exists_e, existential, set_up_ripple] List NewList1,
	ripple_operate Type NewList1 NewList.

compound induction (step_case Type)
        ( cut_meth
	(then_meth
	 (then_meth
           (start_ripple_strat Type)
	   (strat_meth [coerce_vars_control] [ (ripple_synthesis_strat Type),
		 (ripple_strat Type)]))

          (then_meth post_ripple 
		(cond_meth (G\ (Type = exi)) 
			(then_meth (then_meth (try_meth (then_meth (rewrite_with sym_eval_rewrites_list (R:rewrite_rule)) truegoalmeth))
					      (try_meth fertilise))
	                (try_meth (repeat_meth all_e)))

                (try_meth (repeat_meth generalisation_compound)))
		 %% This corresponds to lemma_calculation (I think)
	)))
	_
	true.

/*
compound induction (step_case with_critics)
        ( cut_meth
        (then_meth
          (then_meth (try_meth (repeat_meth all_i)) set_up_ripple)

           (then_meth 
        
            (orelse_meth
              (then_meth
               (then_meth (repeat_meth (then_meth (wave_method outward R) 
                                              (cond_meth contains_meta_var_goal (try_meth ripple_coerce_vars) id_meth)))
                          (try_meth (unblock UR)))
                (orelse_meth (repeat_meth fertilisation_strong)
                 (then_meth     
                   (try_meth (repeat_meth 
                      (then_meth 
                         (then_meth 
                            (then_meth (patch_meth (wave_method inout R1) wave_critic_strat) 
                                       (cond_meth contains_meta_var_goal (try_meth ripple_coerce_vars) id_meth))
                            (try_meth fertilisation_strong))
                      (try_meth (unblock UR1)))))
                   (try_meth fertilise)
                 )
                )
              )
        
             (then_meth 
              (then_meth (repeat_meth 
               (then_meth 
                  (then_meth (patch_meth (wave_method inout R1) wave_critic_strat)
                            (cond_meth contains_meta_var_goal (try_meth ripple_coerce_vars) id_meth))
                   (try_meth fertilisation_strong)))
               (try_meth (unblock UR1)))
              fertilise)
             )

           (then_meth post_ripple (try_meth (repeat_meth generalisation_compound))) 
                 %% This corresponds to lemma_calculation (I think)
        )))
        _
        true.
*/

compound induction fertilise
        ( cut_meth 
%            (orelse_meth
            (repeat_meth (orelse_meth
	       fertilisation_strong		
	       (orelse_meth fertilisation_weak
	       piecewise_fertilisation)))
%			truegoalmeth)
	)
	_
	true.

compound induction (ind_strat whisky_ind)
      ( then_meths (then_meth (try_meth (repeat_meth all_e)) (induction_meth with_critics Scheme Subst))
                   (pair_meth (map_meth id_meth) (map_meth (step_case with_critics))))
	_
	true.

compound induction (ind_strat IndType)
      ( then_meths (then_meth (try_meth (repeat_meth all_e)) (induction_meth IndType Scheme Subst))
                   (pair_meth (map_meth (step_case IndType)) (map_meth id_meth)) )
	_
	true.

% Special case for induction
atomic constructive_logic all_e
        (seqGoal (H >>> G) Context)
        (memb_and_rest (hyp (otype_of X T) _) H NewH, 
	 subterm_of G X _,
	 (not (memb (hyp K An) NewH, not(An = ind_hyp), subterm_of K X _)), 
	 ((memb (hyp K ind_hyp) NewH, subterm_of K X _, NewHyp = H);
	  not ((memb (hyp K ind_hyp) NewH, subterm_of K X _)), NewHyp = NewH),
         forall_elim X T G NewG,
         (not (subterm_of NewG X _)))
        true
        (seqGoal (NewH >>> NewG) Context)
        notacticyet.

end
