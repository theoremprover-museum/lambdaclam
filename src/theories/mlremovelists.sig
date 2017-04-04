/*

File: mlremovelists.sig
Author: Louise Dennis
Description:  Examples taken from an ML exercise.  Many incorrect.
Last Modfied: 11th December 2000

*/

sig mlremovelists.

accum_sig objlists.

type mlremovelists theory.

type mllists indtype.

%% Canonical

type tremoveOne osyn.
type tremoveAll osyn.
type tonceOnly osyn.

type tremoveOne1 rewrite_rule.
type tremoveOne2 rewrite_rule.
type tremoveOne3 rewrite_rule.

type tremoveAll1 rewrite_rule.
type tremoveAll2 rewrite_rule.
type tremoveAll3 rewrite_rule.

type tonceOnly1 rewrite_rule.
type tonceOnly2 rewrite_rule.

type rArA rewrite_rule.


%%%% Common alternative for onceOnly

type tonceOnlya osyn.

type tonceOnlya1 rewrite_rule.
type tonceOnlya2 rewrite_rule.

type onceOnly_query query.

%%%%%%%%

type take osyn.
type drop osyn.
type filt osyn.

type take1 rewrite_rule.
type take2 rewrite_rule.
type take3 rewrite_rule.

type drop1 rewrite_rule.
type drop2 rewrite_rule.
type drop3 rewrite_rule.

type filt1 rewrite_rule.
type filt2 rewrite_rule.
type filt3 rewrite_rule.


%%%%%%%%

type sremoveOne osyn.

type sremoveOne1 rewrite_rule.
type sremoveOne2 rewrite_rule.
type sremoveOne3 rewrite_rule.

type stsimple query.

%%%%%%%%%%%%%%%%%%%

type ml_meth meth.
type ml_ind_strat meth.
type ml_step_case meth.

end
