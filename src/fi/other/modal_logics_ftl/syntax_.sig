sig syntax_.

% --------- individuals and logical formulae

kind iota     type.
kind lformula type.

% --------- logical formula constructors - basic

type not_  lformula -> lformula.
type imp_  lformula -> lformula -> lformula.
type all_  (iota -> lformula) -> lformula.
type box_  lformula -> lformula.
infixr imp_ 3.

% - derived

type and_, or_, iff_  lformula -> lformula -> lformula.
type some_            (iota -> lformula) -> lformula.
type dia_             lformula -> lformula.

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

end
