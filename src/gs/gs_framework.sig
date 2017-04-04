
sig gs_framework.

accum_sig arithmetic.
accum_sig rewriting.
accum_sig constructive_logic.

type gs_framework theory.

type gs_fol theory.
type gs_pure_equality theory.
type gs_objlists theory.
type gs_pna theory.
type gs_pia theory.
type gs_lemmas theory.


type nelson_oppen_style_scheme  (list theory) -> meth.
type shostak_style_scheme  (list theory) -> meth.
type tecton_style_scheme  (list theory) -> meth.

type ccc meth.
type purify (list theory) -> meth.
type purify_e (list theory) -> meth.
type convert_to_cnf meth.
type replace meth.
type repl_eq meth.
type simpl meth.
type simpl_t (theory -> meth).
type check meth.
type lemma_invocation meth.
type entail entailment_type -> (list theory) -> meth.
type valid (list theory) -> meth.

kind entailment_type type.
type nelson_oppen entailment_type.
type shostak entailment_type.
type cooper entailment_type.
type hodes entailment_type.


type decisionSGS01 query.
type decision1 query.
type decision2 query.
type decision3 query.
type decision4 query.
type decision5 query.
type decision6 query.
type decision7 query.
type decision8 query.
type decisionSGS1 query.
type decisionSGS1a query.
type decisionSGS1c query.
type decisionSGS2 query.
type decisionSGS3 query.
type decisionSGS4 query.
type decisionSGS5 query.
type decisionSGS6 query.
type decisionSGS7 query.
type decisionSGS9 query.
type decisionSGS9a query.
type decisionSGS9b query.
type decisionSGS10 query.
type decisionSGS0 query.

type decision_assp query.
type decision_nassp query.
type decisionSGS1b query.


% ******************************************************
%  Theories


type    nat     osyn.

type    zero        osyn.
type    s           osyn.
type    pred        osyn.
type    plus        osyn.
type    leq         osyn.
type    less        osyn.
type    greater     osyn.
type    geq         osyn.
type    times       osyn.


type    olist   osyn -> osyn.
type onil osyn.
type car osyn.
type cdr osyn.
type cons osyn.

type ax1 rewrite_rule.
type ax2 rewrite_rule.
type ax3 rewrite_rule.


% ******************************************************
%  Lemmas

type    min         osyn.
type    max         osyn.

type min_max rewrite_rule.

type minpair osyn.
type maxpair osyn.

type minmaxpairs rewrite_rule.




% ******************************************************
% CNF rule

type gs_prenex_cnf  osyn -> osyn -> o.

type  removeiff  rewrite_rule.
type  removeif  rewrite_rule.
type  thin  rewrite_rule.
type  thin2 rewrite_rule.
type  thin3 rewrite_rule.
type  stratify_neg_univquant  rewrite_rule.
type  stratify_neg_exiquant  rewrite_rule.
type  stratify_and_univquant1  rewrite_rule.
type  stratify_and_univquant2  rewrite_rule.
type  stratify_and_exiquant1  rewrite_rule.
type  stratify_and_exiquant2  rewrite_rule.
type  stratify_or_univquant1  rewrite_rule.
type  stratify_or_univquant2  rewrite_rule.
type  stratify_or_exiquant1  rewrite_rule.
type  stratify_or_exiquant2  rewrite_rule.
type  stratify_neg_and  rewrite_rule.
type  stratify_neg_or  rewrite_rule.
type  stratify_or_and1  rewrite_rule.
type  stratify_or_and2  rewrite_rule.
type  stratify_and_or1  rewrite_rule.
type  stratify_and_or2  rewrite_rule.



% ******************************************************
% Simplification rule

type gs_simplify (list theory) -> osyn -> osyn -> o.
type gs_simpl ((list X) -> (list Y) -> (list Z) -> o).
type gs_simpl_theory osyn -> (list X) -> (list Y) -> o.



% ******************************************************
% Grammars module and support for the absp rule

type gs_abspplus ((list theory) -> (list X) -> osyn -> osyn -> (list U) -> o).
type gs_abspplus_ ((list theory)-> (list X) -> (list Y) -> (list Z) -> (list U) -> o).
type gs_remove_duplicates ((list X) -> (list Y) -> (list Z) -> (list U) -> (list V) -> o).
type gs_abs_one_literal ((list theory) -> (list X)-> osyn -> osyn -> (list X) -> (list Y) -> o).
type gs_abs_one_term (theory -> (list theory) -> (list X)-> osyn -> osyn -> osyn -> (list X) -> (list V) -> o).
type gs_abs_list_of_terms (theory -> (list theory) -> (list X) -> (list X) -> (list Y) -> (list Z) -> (list U) -> (list W) -> o).
type gs_has_otype (theory -> osyn -> osyn -> o).
type gs_var (osyn -> o).
type gs_is_T_term ((list H) -> theory -> osyn -> osyn -> o).
type gs_are_T_terms ((list H) -> theory -> (list X) -> (list Y) -> o).
type gs_is_T_literal ((list H) -> theory -> osyn -> osyn -> o).
type gs_list_of_T_literals  ((list H) -> theory -> (list X) -> (list X) -> o).


% ******************************************************
% Replace rules

type gs_repl osyn -> osyn -> o.
type gs_repl_eq osyn -> osyn -> o.
type gs_repl_ (list X) -> (list Y) -> o.
type gs_repl_one (list X) -> (list Y) -> o.
type gs_repl_eq_ (list X) -> (list Y) -> o.
type gs_repl_eq_one (list X) -> (list Y) -> o.



% ******************************************************
%  Lemma invoking rule

type gs_lemma ((list theory) -> (list Y) -> osyn -> osyn -> (list X) -> o).
type gs_lemma_ ((list theory) -> (list Z) -> (list X) -> (list X) -> (list Y) -> o).


% **************************************************************
%  Entailment

type gs_no_unsat (theory -> (list X) -> o).
type gs_entail (osyn -> (list theory) -> (list X) -> osyn -> osyn -> o).
type gs_entail_no ((list theory) -> (list X) -> osyn -> osyn -> o).
type gs_entail_cooper  ((list H) -> theory -> osyn -> osyn -> o).
type gs_entail_hodes  ((list H) -> theory -> osyn -> osyn -> o).
type gs_entail_shostak ((list H) -> (list theory) -> osyn -> osyn -> o).
type gs_valid  (theory -> (list X) -> o).
type gs_valid_t  ((list H) -> (list theory) -> osyn -> o).
type gs_simplify_t ((list H) -> theory -> osyn -> osyn -> o).


% **************************************************************
%  Constant congruence closure

type gs_ccc (osyn -> osyn -> o).


% **************************************************************
%  Miscellaneous
type gs_same (X -> X -> o).
type gs_same_list ((list X) -> (list Y) -> o). 
type gs_free_var (X -> o).
type gs_member (X -> (list X) -> o).
type gs_diff ((list X) -> (list Y) -> (list X) -> o).
type gs_get_two_members (X -> X -> (list X) -> o).
type gs_occurs (osyn -> osyn -> o).
type gs_occurs_in_list (X -> (list X) -> o).
type gs_delete_from_list ( X -> (list X) -> (list Y) -> o).
type gs_number_of_occs_in_term osyn -> osyn -> int -> o.
type gs_number_of_occs_in_list osyn -> (list X) -> int -> o.
type gs_number_of_literals_in_list (osyn -> (list X) -> int -> o).
type gs_rewrite_with_rules (list rewrite_rule) -> rewrite_rule -> osyn -> osyn -> osyn -> o.
type gs_exhaustivelly_rewrite_with_rules (list rewrite_rule) -> osyn -> osyn -> o.
type gs_exhaustivelly_rewrite_list_with_rules (list rewrite_rule) -> (list X) -> (list Y) -> o. 
type gs_replace_all_in_list osyn -> osyn -> (list X) -> (list Y) -> o.
type gs_replace_all osyn -> osyn -> osyn -> osyn -> o.
type gs_disjunction_to_list_of_literals osyn -> (list X) -> o.
type gs_list_of_literals_to_disjunction (list X) -> osyn -> o.
type gs_convert_to_oyster_syntax (osyn -> string -> o).
type gs_convert_to_oyster_syntax_ (osyn -> string -> o).
type gs_get_lclam_term_from_string (string -> osyn -> o).
type gs_convert_list_to_oyster_syntax ((list X) -> (list Y) -> o).
type gs_get_list_lclam_term_from_string ((list X) -> (list Y) -> o).
type gs_negate_all_literals ((list X) -> (list Y) -> o).
type gs_make_one_string_conj ((list string) -> string -> o).
type gs_make_one_string_conj_ ((list string) -> string -> o).
type gs_make_one_string_disj ((list string) -> string -> o).
type gs_make_one_string_disj_ ((list string) -> string -> o).



% ******************************************
% Sockets
% by Gordon Reid


% To become a client of a Quintus tcp server we need
% to lookup the hostname and port from a file,
% then initialise the connection, then loop.

type gs_string_to_term (string -> X -> o).

type port int -> o.
type externalcall (string -> string -> string -> o).


end
