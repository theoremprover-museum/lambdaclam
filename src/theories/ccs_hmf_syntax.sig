/*

File: ccs_hmf_syntax.sig
Author: James Brotherston
Description: Hennessy-Milner modal logic for describing processes
Last Modified: 25th July 2002

*/

sig ccs_hmf_syntax.

accum_sig list_benchmarks.

type ccs_hmf_syntax theory.


type    action      osyn.
type    tau         osyn.
type    allminus    osyn.
type    co          osyn.

type    hmf         osyn.
type    tt          osyn.
type    ff          osyn.
type    and         osyn.
type    or          osyn.
type    box         osyn.
type    diamond     osyn.
type    exp_box     osyn.
type    exp_diamond osyn.
type    hmf_comp    osyn.

type    ccs         osyn.
type    ccs_nil     osyn.
type    dot         osyn.
type    ccs_plus    osyn.
type    bar         osyn.
type    slash       osyn.

type    satisfies   osyn.

end