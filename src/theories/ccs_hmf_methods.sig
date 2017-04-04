/*

File: ccs_hmf_methods.sig
Author: James Brotherston
Description: Methods and rewrite rules for modal properties of CCS processes
Last Modified: 26th July 2002

*/

sig ccs_hmf_methods.

accum_sig ccs_hmf_syntax.

type  ccs_hmf_methods theory.
type  ccs_hmf_theory  theory.

%% General functions on HM formulas

type  ccs_transition osyn -> osyn -> osyn -> o.
type  hmf_size       osyn -> int -> o.

%% Definition of complementation on HM formulas

type  tt_comp      rewrite_rule.
type  ff_comp      rewrite_rule.
type  and_comp     rewrite_rule.
type  or_comp      rewrite_rule.
type  box_comp     rewrite_rule.
type  diamond_comp rewrite_rule.

%% Atomic methods for satisfaction of modal formulas

type  sat_true     meth.
type  sat_and_i    meth.
type  sat_and_e    meth.
type  sat_or_e     meth.
type  sat_or_i1    meth.
type  sat_or_i2    meth.
type  sat_box      meth.
type  sat_diamond  meth.


%% Defn of exponentiation on modal operators

type  exp_box_base     rewrite_rule.
type  exp_box_step     rewrite_rule.
type  exp_diamond_base rewrite_rule.
type  exp_diamond_step rewrite_rule.

%% Structural induction scheme for HM formulas

type  hmf_struct       scheme.

%% Complete methods for tackling various sorts of problems

type  sat_meth         meth.
type  sat_ind_meth     meth.
type  sat_struct_meth  meth.

%% Logical methods not provided elsewhere

type  iff_i meth.
type  logic_simplify   meth.



end