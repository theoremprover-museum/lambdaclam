%
% PTL decider
%
% types definitions.
%

module types.

% ------------------------------------------
% ------------------------------------ types
% ------------------------------------------

kind formula    type.

type p          string -> formula.

type tt         formula.
type ff         formula.

type neg        formula -> formula.
type and        formula -> formula -> formula.
type or         formula -> formula -> formula.
type imp        formula -> formula -> formula.

type circle     formula -> formula.
type diamond    formula -> formula.
type box        formula -> formula.

type expl        (formula -> formula -> o) -> string -> o.
