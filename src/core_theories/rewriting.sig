/*

File: rewriting.sig
Author: Louise Dennis / James Brotherston
Description: Methods for Symbolic Evaluation.
Last Modified: 15th July 2002

*/

sig rewriting.

accum_sig embed.

type rewriting theory.

%---------------------------------------------
% Method Names
%---------------------------------------------

type taut_sym           meth.
type sym_eval           meth.
type general_rewriting  meth.
type trivials		meth.
type rewrite_with      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_case_split      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_with_hyp   meth.
type rewrite_with_transitive_hyp   meth.
type deploy_lemma       rewrite_rule -> meth.
type unfold_defn        rewrite_rule -> meth. 


%---------------------------------------------

type unpolarise osyn -> osyn -> o.
type multiply_polarities polarity -> polarity -> polarity -> o.


/*  Main rewriting predicates */

%  to allow one-step rewriting with specified rules;
%  second argument is the rule actually used

type rewrite_with_rules (list rewrite_rule) -> rewrite_rule ->
                         osyn -> osyn -> osyn -> o.

type rewrite_with_rules_eval (list rewrite_rule) -> 
                         osyn -> osyn -> osyn -> o.

type rewr rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o.  

type trivial_condition osyn -> (list osyn) -> o.

type bad_for_synthesis rewrite_rule -> osyn -> o.

type rewrite_using osyn -> osyn -> osyn -> mkey -> int -> osyn -> o.
type rewrite_using_transitive osyn -> osyn -> osyn -> mkey -> int -> osyn -> o.
type rewrite_using_once osyn -> osyn -> osyn -> mkey -> int -> osyn -> list int -> list int -> o.

type congr (rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o) ->
            rewrite_rule -> polarity -> osyn -> osyn -> osyn -> list int -> list int -> o. 

type congr_eval (polarity -> osyn -> osyn -> osyn -> o) ->
            polarity -> osyn -> osyn -> osyn -> o. 

type casesplit_analysis (list osyn) -> osyn -> rewrite_rule -> (list osyn) -> (list rewrite_rule -> o) -> o.
  

/* Support for qed command */

kind reasontype type.
type fwd reasontype.
type bwd reasontype.
   
type goal_to_lemma reasontype -> query -> theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.       

   

type formula_tester (list int) -> meth -> truth_label -> meth.
type evaluate meth.
kind truth_label type.

%% Label truth shows whether any
%% subgoals are found to be true, false or undecided.
type label_truth int -> int -> int -> truth_label.

type log_rewrite_rule (list context) -> Rule -> o.
type banned (list rewrite_rule) -> context.
type partition_rw (list A) -> (list A) -> (list A) -> (list A) -> o.


type new_rewrite hyp_ann.
type ind_hyp hyp_ann.
type beta_reduce (list osyn) -> osyn -> osyn -> o.

type db int -> osyn.
type syn_pair osyn -> (list int) -> (list int) -> osyn.
type make_var_pairs int -> (list osyn) -> o.
type count_vars osyn -> osyn -> int -> int -> (list (list osyn)) -> o.
type modify_args osyn -> osyn -> (list osyn) -> o.
type replace_fs osyn -> osyn -> int -> (list (list osyn)) -> o.
type reinstantiate (list (list osyn)) -> (list osyn) -> (list (list osyn)) -> o.

end
