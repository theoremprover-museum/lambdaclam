/*

File: ccs_hmf_theory.sig
Author: James Brotherston
Description: CCS / Hennessy-Milner logic examples from Stirling 2001
Last Modified: 26th July 2002

*/

sig ccs_hmf_theory.

accum_sig ccs_hmf_methods.


type ccs_hmf_theory theory.

%% Type declarations for specific examples

type  cl           osyn.
type  tick         osyn.
type  tock         osyn.
type  cl_def       rewrite_rule.

type  ven          osyn.
type  ven_b        osyn.
type  ven_l        osyn.
type  a1p          osyn.
type  a2p          osyn.
type  big          osyn.
type  little       osyn.
type  collect_b    osyn.
type  collect_l    osyn.
type  ven_def      rewrite_rule.
type  ven_b_def    rewrite_rule.
type  ven_l_def    rewrite_rule.

type  cnt          osyn.
type  up           osyn.
type  down         osyn.
type  cnt_def      rewrite_rule.

type  ct           osyn.
type  round        osyn.
type  ct0_def      rewrite_rule.
type  cti_def      rewrite_rule.

type  crossing     osyn.
type  road         osyn.
type  rail         osyn.
type  signal       osyn.
type  car          osyn.
type  ccross       osyn.
type  train        osyn.
type  tcross       osyn.
type  green        osyn.
type  orange       osyn.
type  crossing_def rewrite_rule.
type  road_def     rewrite_rule.
type  rail_def     rewrite_rule.
type  signal_def   rewrite_rule.

type  cop'         osyn.
type  cop          osyn.
type  in           osyn.
type  out          osyn.
type  no           osyn.
type  cop'_def     rewrite_rule.
type  cop_def1     rewrite_rule.
type  cop_def2     rewrite_rule.

%% Straightforward examples

type  cl_ex1       query.
type  ven_ex1      query.
type  ven_ex2      query.
type  ven_ex3      query.
type  ven_ex4      query.
type  cnt_ex1      query.
type  crossing_ex1 query.
type  crossing_ex2 query.

%% Parameterised induction examples

type  cop_ex1      query.

type  ct_lem1      query.
type  ct_lem2      query.
type  ct_lem3      query.
type  plus_lem1    rewrite_rule.
type  ct_ex1       query.

%% Structural induction examples

type  hmf_comp1    query.

type  sat_false    rewrite_rule.

end