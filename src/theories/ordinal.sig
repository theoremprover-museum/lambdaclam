/*

File: ordl.sig
Author: Louise Dennis
Description: A theory of Ordinals
Last Modified: 20th March 2001

*/

sig ordinal.

accum_sig arithmetic.
accum_sig constructive_logic.

type ordinal theory.

type    ordl    osyn.  

type 	ord_zero osyn.
type 	ord_s osyn.
type    lim          osyn.
type 	ord_plus osyn.
type 	ord_times osyn.
type	ord_exp osyn.
type ord_leq osyn.

type    ord_plus1           rewrite_rule.
type    ord_plus2           rewrite_rule.
type    ord_plus3           rewrite_rule.
type    ord_exp1            rewrite_rule.
type    ord_exp2            rewrite_rule.
type    ord_exp3            rewrite_rule.
type    ord_times1          rewrite_rule.
type    ord_times2          rewrite_rule.
type    ord_times3          rewrite_rule.
type    lim_lim         rewrite_rule.
type    lim_suc         rewrite_rule.
type    lim1            rewrite_rule.
type    lim2            rewrite_rule.
type    lim3            rewrite_rule.
type    ord_leq1            rewrite_rule.
type    ord_leq2            rewrite_rule.
type    ord_leq_ss            rewrite_rule.
type    leq3            rewrite_rule.
type    leq4            rewrite_rule.
type    leq5            rewrite_rule.
type 	ord_plus_functional rewrite_rule.
type 	ord_times_functional rewrite_rule.
type 	ord_s_functional	rewrite_rule.

type asspord        query.
type plus0ord       query.
type leqsumord      query.
type distord        query.
type assmord        query.
type times1ord      query.
type expplusord     query.
type exptimesord    query.
type leqsucord      query.
type leqreflord     query.

type ordl_ind 	scheme.

type  times2ord  query.
type  exp2ord  query.
type  exp1ord  query.
type  leqsumord2  query.
type  times1leftord  query.
type  times0leftord  query.
type  plus1rightord  query.
type  exp1ord2  query.

type leq_refl rewrite_rule.
type lim1leq rewrite_rule.

type iter osyn.
type omega osyn.
type alph osyn.
type phi osyn.

type iter_lemma rewrite_rule.
type omega_lemma rewrite_rule.
type continuity_lemma rewrite_rule.

type iterlemma query.
type fixpoint query.

type fixpoint_top_meth meth.
type triv_eq meth.

type ground_eq osyn -> osyn -> o.

end
