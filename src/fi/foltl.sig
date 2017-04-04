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
% Operators/connectives
%----------------------------------

type    multi   (list osyn) -> osyn.

type    @       osyn.
type    lform   osyn.
type    box     osyn.
type    dia     osyn.
type    next    osyn.
type    boxt    osyn.
type    until   osyn.
type    wuntil  osyn.

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
type mlwuntil   int -> meth.
type mrwuntil   int -> meth.
type mlboxt     int -> meth.
type mrboxt     int -> meth.
type mlnext     int -> meth.
type mrnext     int -> meth.
type mlleq      int -> meth.
type mrleq      int -> meth.

type foltl_taut meth.

type wrapTheta  theta -> osyn.

end
