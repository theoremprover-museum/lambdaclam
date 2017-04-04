/* ----------------------------------

File: bridge.sig
Author: Claudio Castellini
Last Modified: May 2002

------------------------------------- */

sig bridge.
accum_sig fi.

type translate_plan        cplan -> (goal_ -> goal_ -> o) -> o.
type translate_formula     osyn -> formula -> o.
type translate_lformula    osyn -> lformula -> o.
type translate_theta       osyn -> theta -> o.
type proofcheck            cplan -> query -> o.
type wrap_SF               osyn -> lformula.
type wrap_P                osyn -> iota.
type wrap_P1               osyn -> (iota -> lformula).
type wrap_P2               osyn -> (iota -> iota -> lformula).
type wrap_P3               osyn -> (iota -> iota -> iota -> lformula).
type wrap_T                osyn -> theta.

type convHyps              (list osyn) -> osyn -> o.

end
