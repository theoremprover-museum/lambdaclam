/*

File: lim_plus.sig
Author: Louise Dennis
Description: Lim Plus example (for embeddings paper)

*/

sig lim_plus.
accum_sig arithmetic.
accum_sig constructive_logic.

type lim_plus theory.

type lim osyn.
type mod osyn.
type less osyn.

type lim1 rewrite_rule.
type minus_plus rewrite_rule.
type mod_plus_less rewrite_rule.
type half_plus_less rewrite_rule.
type forall_and rewrite_rule.
type exists_less_and rewrite_rule.
type less_half_and rewrite_rule.

type lim_plus_meth meth.

type lim_plus_thm query.
type lim_minus_thm query.

type set_up_ripple_no_ind meth.

type testthm query.

end
