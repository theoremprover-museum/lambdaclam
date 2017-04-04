/* ----------------------------------

File: foltl.sig
Author: Claudio Castellini
Description: Labelled theory of First-Order Linear Temporal
             Logic. Based upon Louise's hol.mod & hol.sig
Last Modified: September 2002

------------------------------------- */

sig foltl.
accum_sig arithmetic.
accum_sig ftl.

type foltl theory.

type wrap_tac    (goal_ -> goal_ -> o) -> tactic.
type wrap3F_tac  ((goal_ -> goal_ -> o) ->
                 ((goal_ -> goal_ -> o) ->
                 ((goal_ -> goal_ -> o) -> (goal_ -> goal_ -> o)))) -> tactic.

%----------------------------------
% Queries
%----------------------------------

type  ppp  osyn.
type  ppq  osyn.
type  ppf  osyn.
type  ppg  osyn.
type  ppr  osyn.
type  pps  osyn.

type  easy01         query.
type  easy02         query.
type  easy03         query.
type  easy04         query.
type  easy05         query.
type  easy06         query.
type  easy07         query.
type  necessitation  query.
type  duality        query.
type  seriality      query.
type  reflexivity    query.
type  transitivity   query.
type  directedness   query.
type  connectedness  query.
type  barcan         query.
type  induction1     query.
type  induction2     query.
type  induction3     query.
type  induction4     query.
type  induction5     query.

%----------------------------------
% Operators/connectives
%----------------------------------

type    multi   (list osyn) -> osyn.

type    pwit    osyn.
type    pcv     osyn.
type    pla     osyn.
type    phb     osyn.
type    @       osyn.
type    lform   osyn.
type    box     osyn.
type    dia     osyn.
type    next    osyn.
type    boxt    osyn.
type    until   osyn.

%----------------------------------
% Rewrite rules
%----------------------------------

type  leq_1  rewrite_rule.
type  leq_2  rewrite_rule.

%----------------------------------
% Methods
%----------------------------------

type membN      int -> A -> (list A) -> o.

type max        int -> int -> meth.
type mlnot      int -> meth.
type mrnot      int -> meth.
type mlimp      int -> meth.
type mrimp      int -> meth.
type mlall      int -> meth.
type mrall      int -> meth.
type mrbox      int -> meth.
type mlbox      int -> meth.

type mliff      int -> meth.
type mriff      int -> meth.
type mland      int -> meth.
type mrand      int -> meth.
type mlor       int -> meth.
type mror       int -> meth.
type mlsome     int -> meth.
type mrsome     int -> meth.
type mrdia      int -> meth.
type mldia      int -> meth.

type ment       meth.

type mrefl      meth.
type mtrans     meth.
type msconn     (osyn -> osyn -> meth).

type mluntil    int -> meth.
type mruntil    int -> meth.
type mlboxt     int -> meth.
type mrboxt     int -> meth.
type mlnext     int -> meth.
type mrnext     int -> meth.
type mlleq      int -> meth.
type mrleq      int -> meth.

type foltl_taut meth.

type wrap_T     osyn -> theta.

end
