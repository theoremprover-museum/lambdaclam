module control_divides.

accumulate arithmetic.
accumulate constructive_logic.

/*
local control_dividesdummy osyn -> o.
control_dividesdummy X.
*/

has_otype control_divides divides (arrow [nat, nat] bool).
has_otype control_divides iff (arrow [bool, bool] bool).

definition control_divides iff1 
	trueP
	(app iff  [A, B])
	(app and  [(app imp  [A, B]),
			 (app imp  [B, A])]).

definition control_divides divides_def
	trueP
	(app divides  [A, B])
	(app exists  [nat, (abs (c\
		(app eq  [B, (app otimes  [A, c])])) nat)]).

lemma control_divides times1right equiv
	trueP
	(app otimes [_, zero])
	zero.
lemma control_divides ass_otimes equiv
	trueP
	(app otimes [(app otimes [X, Y]), Z])
	(app otimes [X, (app otimes [Y, Z])]).

control_rule_for control_divides iff_control (seqGoal (Hyps >>> (app iff L)) C) List NewList:-
		 prefer [(rewrite_with _ iff1)] List NewList.
control_rule_for control_divides divides_control (seqGoal (Hyps >>> G) C) List NewList:-
		 subterm_of G divides _,
		 prefer [(rewrite_with _ divides_def)] List NewList.
control_rule_for control_divides imp_i_control (seqGoal (Hyps >>> (app imp L)) C) List NewList:-
		 prefer [imp_i] List NewList.
control_rule_for control_divides all_i_control (seqGoal (Hyps >>> (app forall L)) C) List NewList:-
		 prefer [all_i] List NewList.
control_rule_for control_divides and_i_control (seqGoal (Hyps >>> (app and L)) C) List NewList:-
		 prefer [and_i] List NewList.
control_rule_for control_divides and_e_control (seqGoal (Hyps >>> G) C) List NewList:-
		 memb (hyp (app and [A, B]) _) Hyps,
		 prefer [and_e] List NewList.
control_rule_for control_divides exists_e_control (seqGoal (Hyps >>> G) C) List NewList:-
		 memb (hyp (app exists L) _) Hyps,
		 prefer [exists_e] List NewList.
control_rule_for control_divides exists_i_control (seqGoal (Hyps >>> (app exists L)) C) List NewList:-
		 prefer [exists_i] List NewList.
control_rule_for control_divides non_instantiating_rewrite (seqGoal (Hyps >>> G) C) List NewList:-
		 subterm_of G ST Pos,
		 not (contains_meta_var_term ST),
		 sym_eval_rewrites_list L,
		 memb R L,
		 rewr R _ ST _ _,
		 prefer [(rewrite_at_pos _ R Pos)] List NewList.
control_rule_for control_divides instantiating_rewrite (seqGoal (Hyps >>> G) C) List NewList:-
		 copy_term [G] [G1],
		 subterm_of G1 ST Pos,
		 not (headvar_osyn ST),
		 contains_meta_var_term ST,
		 sym_eval_rewrites_list L,
		 memb R L,
		 rewr R _ ST _ _,
		 prefer [rewrite_with_hyp, (rewrite_at_pos _ R Pos)] List NewList.

compound control_divides divides_meth
	(repeat_meth (strat_meth 
         [iff_control, divides_control, imp_i_control, 
          all_i_control, and_i_control, and_e_control, 
          exists_i_control, exists_e_control, 
          non_instantiating_rewrite, instantiating_rewrite] 
         [trivial, rewrite_with_hyp, (rewrite_with sym_eval_rewrites_list _), exists_i,  
          exists_e, and_i, (rewrite_at_pos sym_eval_rewrites_list _ _),
           and_e, all_i, imp_i]))	_
	true.


%% Consider putting in rewriting.
atomic control_divides (rewrite_at_pos ListPredicate Rule nil)
        ( seqGoal (H >>> G) Context)
        (ListPredicate List,
		 copy_term [G] [G1],
         memb Rule List,
         rewr Rule _ G1 RHS C,
         trivial_condition C H,
         (env_otype RHS H _))
                              % check the condition is in the hypotheses
        true
        (seqGoal (H >>> RHS) Context)
        notacticyet.
atomic control_divides (rewrite_at_pos ListPredicate Rule TermPos)
        ( seqGoal (H >>> G) Context)
        (ListPredicate List,
         (congr (R\ P\ LHS\ RHS\ C\
               (memb R List,
               rewr R P LHS RHS C)) Rule positive_polarity G G1 Cond [] TermPos,
         (trivial_condition Cond H,
         (env_otype G1 H _))))
                              % check the condition is in the hypotheses
        true
        (seqGoal (H >>> G1) Context)
        notacticyet.
change_method_vars (rewrite_at_pos ListPredicate Rule TermPos) (rewrite_at_pos ListPredicate _ _):- !.

atomic control_divides exists_e
	(seqGoal (H >>> G) Context)
	(memb_and_rest (hyp (app exists [Type, (abs Term Type)]) Ann) H Rest)
	true
	(allGoal Type (x\ (seqGoal ((hyp (otype_of x Type) nha)::((hyp (Term x) Ann)::Rest) >>> G) Context)))
	notacticyet.


top_goal control_divides zero_divides []
	(app forall  [nat, (abs (x\
		(app iff  [
			(app divides  [zero, x]),
			(app eq  [x, zero])])) nat)]).

top_goal control_divides divides_zero []
	(app forall [nat, (abs (x\ (app divides [x, zero])) nat)]).

top_goal control_divides divides_one []
	(app forall  [nat, (abs (x\
		(app iff  [
			(app divides  [(app s [zero]), x]),
			(app eq  [x, (app s [zero])])])) nat)]).

top_goal control_divides divides_trans []
	(app forall [nat, (abs (a\
	(app forall [nat, (abs (b\
	(app forall [nat, (abs (c\
	(app imp [(app and [(app divides [a, b]), (app divides [b, c])]), (app divides [a, c])])) nat)])) nat)])) nat)]).

top_goal control_divides divides_plus []
	(app forall [nat, (abs (d\
	(app forall [nat, (abs (a\
	(app forall [nat, (abs (b\
	(app imp [(app and [(app divides [d, a]), (app divides [d, b])]), (app divides [d, (app plus [a, b])])])) nat)])) nat)])) nat)]).


top_goal control_divides divides_sub []
	(app forall [nat, (abs (d\
	(app forall [nat, (abs (a\
	(app forall [nat, (abs (b\
	(app imp [(app and [(app divides [d, a]), (app divides [d, b])]), (app divides [d, (app minus [a, b])])])) nat)])) nat)])) nat)]).

top_goal control_divides divides_lmul []
	(app forall [nat, (abs (d\
	(app forall [nat, (abs (a\
	(app forall [nat, (abs (x\
	(app imp [(app divides [d, a]), (app divides [d, (app otimes [x, a])])])) nat)])) nat)])) nat)]).

top_goal control_divides divides_rmul []
	(app forall [nat, (abs (d\
	(app forall [nat, (abs (a\
	(app forall [nat, (abs (x\
	(app imp [(app divides [d, a]), (app divides [d, (app otimes [a, x])])])) nat)])) nat)])) nat)]).

benchmark_plan control_divides Meth Query :-
        testloop (%interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (set_sym_eval_list [idty, s_functional, divides_def, ass_otimes, times1right],
        (add_theory_defs_to_sym_eval_list arithmetic,
        pds_plan Meth Query))
        )).

change_method_vars X X.

end
	
