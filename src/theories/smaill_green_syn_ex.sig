/*

File: smaill_green_syn_ex.sig
Author: Louise Dennis

Description:  Synthesis Example from Smail and Green, Higher-Order Annotated Terms for Proof Search.

*/

sig smaill_green_syn_ex.
accum_sig list_benchmarks.
%% accum_sig constructive_logic.

type smaill_green_syn_ex theory.

type synthesis_thm query.
type sqr query.
type tcons query.
type sg_cons query.
type sg_app query.
type sg_syn4 query.
type sg_pair query.
type sg_asps query.
type sg_pair2 query.
type sg_half query.
type sg_even query.

type omem4 rewrite_rule.
type ass_or rewrite_rule.
type prop1 rewrite_rule.
type singleton rewrite_rule.
type exists_or_l rewrite_rule.
type exists_or_r rewrite_rule.

type exi_induction_top indtype -> meth.
type sym_eval_exi meth.
type rewrite_with_exi (list rewrite_rule -> o) -> rewrite_rule -> meth.

type set_up_ex_ripple int -> meth.
type ex_wave_method dir -> rewrite_rule -> meth.

end
