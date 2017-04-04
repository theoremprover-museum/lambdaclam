/*

File: synthesis_ex.sig
Author: Louise Dennis

Description:  Synthesis Example from Smail and Green, Higher-Order Annotated Terms for Proof Search.

*/

sig synthesis_ex.
accum_sig list_benchmarks.

type synthesis_ex theory.

type synthesis_thm query.

type omem4 rewrite_rule.
type ass_or rewrite_rule.
type prop1 rewrite_rule.

type exi indtype.

type set_up_ex_ripple int -> meth.
type ex_wave_method dir -> rewrite_rule -> meth.


end
