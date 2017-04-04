/*

File: wave_critics.sig
Author: Louise Dennis / James Brotherston
Description: Induction engine including Andrew Ireland's critics
Last Modified: 21st August 2002

*/

sig wave_critics.

%% The signature for the induction engine is the signature for the 
%% logic_eq_constants module, which also contains various pretty-printing 
%% and syntax declarations, plus the signature for the pairing type, plus 
%% various things from the modules which do rewriting, induction and so on.

accum_sig logic_eq_constants, pairs.

kind branch_var_status type.

type so branch_var_status.
type ind_var branch_var_status.
type ind_var_nowf branch_var_status.

%% From module: generalise

type gen         theory.
type generalise	 meth.
type generalisation_compound meth.

%% From module: embed

type embeds      etree -> osyn -> osyn -> o.

type nwf dir.
type uiwf dir.
type uowf dir.
type lo dir.
type li dir.
type new dir.
type pnew dir.

%% From module: rewriting

type rewriting   theory.

type sym_eval           meth.
type general_rewriting  meth.
type rewrite_with      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_case_split      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_with_hyp   meth.
type rewrite_with_transitive_hyp   meth.
type deploy_lemma       rewrite_rule -> meth.
type unfold_defn        rewrite_rule -> meth. 
type rewrite_with_rules (list rewrite_rule) -> rewrite_rule ->
                         osyn -> osyn -> osyn -> o.
type rewrite_with_rules_eval (list rewrite_rule) -> 
                         osyn -> osyn -> osyn -> o.
type rewr rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o.  

type trivial_condition  osyn -> (list osyn) -> o.
type bad_for_synthesis  rewrite_rule -> osyn -> o.

kind reasontype type.
type fwd        reasontype.
type bwd        reasontype.
   
type goal_to_lemma reasontype -> query -> theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.          

type congr (rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o) ->
            rewrite_rule -> polarity -> osyn -> osyn -> osyn -> list int -> list
 int -> o. 

type beta_reduce (list osyn) -> osyn -> osyn -> o.
type log_rewrite_rule (list context) -> Rule -> o.

type rewrite_using osyn -> osyn -> osyn -> mkey -> int -> osyn -> o.
type rewrite_using_transitive osyn -> osyn -> osyn -> mkey -> int -> osyn -> o.


%% From module: schemes

type measured       osyn -> (osyn -> osyn) -> osyn.
type free           osyn -> (osyn -> osyn) -> osyn.

%% From module: wave

type wave theory.

kind ripFail type.

type failed_sink etree -> osyn -> ripFail.
type failed_embed rewrite_rule -> ripFail.

type wave_method      dir -> rewrite_rule ->  meth.
type wave_case_split  rewrite_rule -> meth.

type check_wave_case_split rewrite_rule -> crit.
type wave_critic_strat crit.
type wave_patch        ripFail -> (list int) -> rewrite_rule -> crit.
type wave_failure      ripFail -> rewrite_rule -> crit.

type ripple_rewrite (list osyn) -> rewrite_rule -> (pairing osyn (list etree)) -> (pairing osyn (list etree)) -> osyn -> (list int) -> dir -> (list context) -> int -> o.

type sinkable etree -> (list int) -> o.

type embeds_list (list etree) -> osyn -> (list etree) -> (list etree) -> (list etree) -> o.
type measure_check  dir -> (list etree) -> (list etree)  -> (list int) -> (list etree) -> int -> o.

type strip_forall_embeds osyn -> etree -> osyn -> o.

type ind_hyp hyp_ann.
type wrule hyp_ann.
type new_rewrite hyp_ann.

type induction_hypothesis (list osyn) -> (list osyn) -> (list osyn) -> o.

type set_up_ripple     meth.   % meta-level step (find embedding)
type post_ripple       meth.   % meta-level step (throw away embedding)

%% From module: pwf

type pwf theory.

type piecewise_fertilisation meth.
type imp_ifert meth.
type or_fert meth.

type wrule hyp_ann.

%% From module: unblocking

type unblocking theory.
type unblock rewrite_rule ->  meth.

%% From module: induction

type induction theory.

type wave_rule osyn -> rewrite_rule.
type contains_any_meta_var_goal goal -> o.

kind indtype type.

type exi indtype.
type normal_ind   indtype.
type with_critics indtype.
type whisky_ind   indtype.
type sym_eval_crit indtype.
type error_loc indtype.
type lim_thm indtype.

type induction_meth        indtype -> scheme -> subst ->  meth.
type fertilise             meth.
type fertilisation_strong  meth.
type fertilisation_weak    meth.
type truegoalmeth	     meth.

type induction_top indtype -> meth.
type ind_strat     indtype -> meth.
type step_case     indtype -> meth.
type ripple_strat indtype -> meth.
type start_ripple_strat indtype -> meth.
type ripple_coerce_vars meth.
type check_embedding meth.

type ripple_operate indtype -> (list meth) -> (list meth) -> o.
type ripple_set_up indtype -> control_rule.

type trivials           meth.
type equality_condition meth.

type triv_abs rewrite_rule.

type sink_match_     osyn -> osyn -> osyn -> (list osyn) -> o.

%% NB: nothing required from module: casesplit

%% From this module

type induction_revision   meth -> (list int) -> crit.	
type generalisation_AI    etree -> osyn -> osyn -> crit.

type newgen osyn -> osyn -> context.

type introduce_lemma osyn -> meth.
type introduce_gen   osyn -> meth.

type fun_iter     osyn.
type fun_compose  osyn.
type nat          osyn.

type previous_casesplit rewrite_rule -> crit.
/*
type lemma_calculation osyn -> crit.
type introduce_discovered_lemma osyn -> meth.
*/
%% From module coerce_meta_vars

type coerce_meta_vars theory.

type coerce_vars meth.
type try_projection meth.


%% From module conjecture_tester

kind truth_label type.

%% Label truth shows whether any
%% subgoals are found to be true, false or undecided.
type label_truth int -> int -> int -> truth_label.
type banned (list rewrite_rule) -> context.

type conjecture_tester theory.

type formula_tester (list int) -> meth -> truth_label -> meth.
type generate_ground_instances (list int) -> meth.
type pick_label (truth_label) -> meth.
type evaluate meth.
type type_constructors rewrite_rule.
type contains_meta_var_goal goal -> o.

type beta_reduction rewrite_rule.
type imp1 rewrite_rule.
type imp2 rewrite_rule.
type imp3 rewrite_rule.
type and1 rewrite_rule.
type and2 rewrite_rule.
type and3 rewrite_rule.
type and4 rewrite_rule.
type or1 rewrite_rule.
type or2 rewrite_rule.
type or3 rewrite_rule.
type or4 rewrite_rule.
type neg1 rewrite_rule.
type neg2 rewrite_rule.
type iff1 rewrite_rule.

kind embedding_status type.
type nu embedding_status.
%% no unaccounted for wave fronts
type si embedding_status.
%% surplus inward wave front.
type do embedding_status.
%% deficit outward wave front.
end
