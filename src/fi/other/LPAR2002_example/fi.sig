sig fi.

accum_sig foltl.

type fi theory.
type mymappred2 (A -> B -> o) -> (list A) -> (list B) -> o.

kind feature            type.

type acr                feature.
type cfbl               feature.

type system_axioms      (list (osyn -> osyn -> osyn -> osyn)) -> o.
type strip_invariant    osyn -> osyn -> osyn -> osyn -> osyn -> osyn -> o.
type define_invariant   (osyn -> osyn -> osyn -> osyn) -> osyn -> o.
type define_feature     feature -> osyn -> (list (osyn -> osyn -> osyn -> osyn)) -> o.
type define_interaction feature -> feature -> query.
type is_feature         feature -> (list (osyn -> osyn -> osyn -> osyn)) -> o.

type user               osyn.

type me                 osyn.
type you                osyn.

type has_acr            osyn.
type has_cfbl           osyn.
type idle               osyn.
type onhook             osyn.
type dn_allowed         osyn.
type call_req           osyn.
type acr_announce       osyn.
type forwarding         osyn.

type fi_casesplit       meth.
type fi_firstorder      meth.
type fi_propositional   meth.
type fi_complete        meth.

type toy_top_goal        query.
type toy_top_goal1       query.
type toy_top_goal2       query.
type toy_casesplit       meth.
type toy_propositional   meth.
type toy_complete        meth.

end
