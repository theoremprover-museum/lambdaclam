/* 

File: induction.sig
Author: Louise Dennis / James Brotherston
Description: Induction Methods
Last Modified: 20th August 2002

*/

sig induction.

accum_sig schemes, generalise, pwf.

type induction theory.

kind indtype type.

type   exi indtype.
type   normal_ind   indtype.
type   with_critics indtype.
type   whisky_ind   indtype.
type sym_eval_crit indtype.
type error_loc indtype.
type lim_thm indtype.

type   induction_meth        indtype -> scheme -> subst ->  meth.
type   fertilise             meth.
type   fertilisation_strong  meth.
type   fertilisation_weak    meth.
type   truegoalmeth	     meth.

%% New more "generic" version

type induction_top indtype -> meth.
type ind_strat     indtype -> meth.
type step_case     indtype -> meth.
type ripple_strat  indtype -> meth.
type start_ripple_strat  indtype -> meth.
type ripple_synthesis_strat  indtype -> meth.
type ripple_coerce_vars meth.
type check_embedding meth.

%% type trivials           meth.
type equality_condition meth.

type triv_abs rewrite_rule.

type sink_match_     osyn -> osyn -> osyn -> (list osyn) -> o.

type coerce_vars_control control_rule.
type inward_ripple indtype -> control_rule.
type outward_ripple indtype -> control_rule.
type ripple_set_up indtype -> control_rule.

type ripple_operate indtype -> (list meth) -> (list meth) -> o.
type after_fertilisation control_rule.

end
