module syntax.

% --------- static formulae

kind i          type.
kind sformula   type.

type false             sformula.
type neg               sformula -> sformula.
type and, or, imp, iff sformula -> sformula -> sformula.
type forall, exists    (i -> sformula) -> sformula.
type next, evt, glob   sformula -> sformula.

infixl  and   6.
infixl  or    5.
infixr  imp   3.
infixr  iff   3.

% --------- labelled formulae

kind formula    type.
kind time       type.

type    @     sformula -> time -> formula.
infixr  @     2.

% --------- sequents, proofs, goals

kind  goal       type.
kind  proof      type.
kind  sequent    type.

type  -->        (list formula) -> (list formula) -> sequent.
type  proves     proof -> sequent -> goal.

infix -->        4.
infix proves     3.
