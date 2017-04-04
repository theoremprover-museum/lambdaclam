sig syntax_.

% --------- individuals and logical formulae

kind user_    type.
kind nat_     type.
kind lformula type.

% --------- logical formula constructors - basic

type z_    nat_.
type s_    nat_ -> nat_.
type eq_   nat_ -> nat_ -> lformula.
infixr eq_ 2.

type not_  lformula -> lformula.
type imp_  lformula -> lformula -> lformula.
type allU_ (user_ -> lformula) -> lformula.
type allN_ (nat_ -> lformula) -> lformula.
type box_  lformula -> lformula.
infixr imp_ 3.

% - derived

type and_   lformula -> lformula -> lformula.
type or_    lformula -> lformula -> lformula.
type iff_   lformula -> lformula -> lformula.
type someU_ (user_ -> lformula) -> lformula.
type someN_ (nat_ -> lformula) -> lformula.
type dia_   lformula -> lformula.

infixl and_ 6.
infixl or_  5.
infixr iff_ 3.

% --------- labelled formulae and worlds

kind formula  type.
kind theta    type.

type at_      lformula -> theta -> formula.
infixr at_ 2.

% --------- sequents, proofs, goals, goal constructors

kind sequent    type.
kind proof      type.
kind goal_      type.

type --> (list formula) -> (list formula) -> sequent.
infix --> 4.
type proves proof -> sequent -> goal_.
infix proves 3.

type true_goal     goal_.
type and_goal      goal_ -> goal_ -> goal_.
type forall_goal   (I -> goal_) -> goal_.

% --------- additional operators for FI (LPAR paper)

type next_ lformula -> lformula.
type boxt_ theta -> lformula -> lformula.
type until_ lformula -> lformula -> lformula.
infixr until_ 4.
type wuntil_ lformula -> lformula -> lformula.
infixr wuntil_ 4.

end
