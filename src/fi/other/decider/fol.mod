%
% a tactic-based theorem prover for FOL.
%
% source: Felty, tutorial on lambda-prolog and its applications
%

module fol.

kind form       type.
kind nprf       type.
kind i          type.

% ------- basic operators

type and, or, imp       form -> form -> form.
type neg                form -> form.
type forall             (i -> form) -> form.
type exists             (i -> form) -> form.
type false              form.

infixl  or  4.
infixl  and 5.
infixr  imp 6.

% ------- constants

type c i.
type f i -> i -> i.
type q form.
type p i -> form.

% for instance, (forall x\(exists y\((p x) imp (p y)))).

%
% ************** natural deduction rules.
%

type proof      nprf -> form -> o.
type and_i      nprf -> nprf -> nprf.
type or_i       nprf -> nprf.
type exists_i   nprf -> nprf.
type forall_i   nprf -> nprf.
type imp_i      nprf -> nprf.

proof (and_i P1 P2) (A and B) :- proof P1 A, proof P2 B.     % and-i
proof (or_i P) (A or B) :- proof P A; proof P B.             % or-i
proof (exists_i P) (exists A) :- proof P (A T).              % existential introduction.
proof (forall_i P) (forall A) :- pi y\(proof (P y) (A y)).   % universal introduction.
proof (imp_i P) (A imp B) :-
        pi pA\((proof pA A) => (proof (P pA) B)).            % discharge of assumptions











