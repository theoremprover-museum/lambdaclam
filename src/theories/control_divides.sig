sig control_divides.

accum_sig arithmetic.
accum_sig constructive_logic.

type control_divides theory.

type divides osyn.
type iff osyn.

type divides_meth meth.

type  iff_control  control_rule.
type  divides_control  control_rule.
type  imp_i_control  control_rule.
type  all_i_control  control_rule.
type  and_i_control  control_rule.
type  and_e_control  control_rule.
type  exists_i_control  control_rule.
type  exists_e_control  control_rule.
type  non_instantiating_rewrite  control_rule.
type  instantiating_rewrite  control_rule.

type  exists_e meth.
type  rewrite_at_pos  ((list rewrite_rule -> o) -> rewrite_rule -> (list int) -> meth).

type divides_def rewrite_rule.
type times1right rewrite_rule.
type ass_otimes rewrite_rule.

type divides_zero query.
type zero_divides query.
type divides_one query.
type divides_trans query.
type divides_plus query.
type divides_sub query.
type divides_lmul query.
type divides_rmul query.

end