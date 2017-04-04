sig fi.

accum_sig foltl.

type fi theory.

type mymappred2          (A -> B -> o) -> (list A) -> (list B) -> o.
type disjunct_of         lformula -> lformula -> o.

type user                osyn.
type translate_formula   osyn -> formula -> o.

type at          nat_ -> user_ -> lformula.

type idle        user_ -> lformula.
type dialling    user_ -> lformula.
type connecting  user_ -> user_ -> lformula.
type unavailable user_ -> lformula.

type offhook     user_ -> lformula.
type onhook      user_ -> lformula.
type dial        user_ -> user_ -> lformula.

type fi_triv_1     query.
type fi_triv_2     query.
type fi_triv_3     query.
type fi_triv_4     query.

type fi_exists_path       meth.

type fi_prove_init        int -> meth.
type fi_find_cons         int -> meth.
type fi_find_progress     int -> meth.
type fi_find_loop         int -> meth.

end
