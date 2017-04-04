/* ----------------------------------

File: bridge.sig
Author: Claudio Castellini
Last Modified: May 2002

------------------------------------- */

sig bridge.
accum_sig fi.

type lfvar                   A -> o.
type osynvar                 A -> o.
type lfconst1,lfconst2       lformula.
type osynconst1,osynconst2   osyn.

type translate_plan        cplan -> (goal_ -> goal_ -> o) -> o.
type translate_formula     osyn -> formula -> o.
type translate_lformula    osyn -> lformula -> o.
type translate_theta       osyn -> theta -> o.
type proofcheck            cplan -> query -> o.

type wrapAtom              lformula -> osyn.
type wrapAtom1             (TYPE1 -> lformula) -> osyn.
type wrapAtom2             (TYPE1 -> TYPE2 -> lformula) -> osyn.
type wrapAtom3             (TYPE1 -> TYPE2 -> TYPE3 -> lformula) -> osyn.
type wrapTheta             theta -> osyn.
type wrapIota              TYPE -> osyn.

type convHyps              (list osyn) -> osyn -> o.

type www lformula.

end
