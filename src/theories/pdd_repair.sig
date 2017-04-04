sig pdd_repair.

accum_sig objlists.

type pdd_repair theory.




type my_sym_eval meth.
type stop_meth meth.
type introduce_hyp osyn -> meth.
type introduce_hyp_and_ban osyn -> rewrite_rule -> meth.

type sym_eval_crit_strat crit.
type sym_eval_critic int -> osyn -> rewrite_rule -> crit.

type pdd_critic osyn -> rewrite_rule -> crit.
type pdd_critic_strat crit.

type andlem rewrite_rule.

type known_false osyn -> o.

type db int -> osyn.
type roll_back_to_start crit.


end
