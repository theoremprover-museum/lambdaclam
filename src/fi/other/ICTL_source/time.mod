module time.

accumulate basics.
accumulate syntax.

%
% ------- basic definitions
%

type z           time.
type s           time -> time.
type wafter      time -> time -> o.

infixr wafter  3.

%
% ------- metapredicate var(.)
%

type istvar, isntvar   time -> o.

istvar T :- not(not(T = z)), not(not(T = (s z))).
isntvar T :- not(istvar T).

%
% ------- little metainterpreter enforcing wafter's properties
%

type check  o -> int -> o.
type conv   time -> time -> time -> time.

check (Tau wafter z) _.                         % well-foundedness

check (Tau wafter Tau) _.                       % reflexivity

check (Tau wafter Tau') 0 :-                    % transitivity
  sigma tau''\ (check (Tau wafter tau'') 1,
                not(Tau = tau''),
                check (tau'' wafter Tau') 0 ).

%check ((conv T T1 T2) wafter T1) 0 :-           % convergency
%  check (T1 wafter T) 1,
%  check (T2 wafter T) 1,
%  not(T1 = T2).
%check ((conv T T1 T2) wafter T2) 0 :-
%  check (T1 wafter T) 1,
%  check (T2 wafter T) 1,
%  not(T1 = T2).

check (Tau wafter Tau') 0 :-                     % linearity?
  not(not(Tau = Tau'));
  not(check (Tau' wafter Tau) 1).

check (Tau wafter (s Tau)) _ :-                  % discreteness?
  !, fail.
check ((s Tau) wafter Tau) _.
check (Tau' wafter (s Tau)) N :-
  check (Tau' wafter Tau) N,
  not(Tau' = Tau).

% entailment checking procedure

kind answer  type.

type   constraint    o -> formula.
type   yes, no       answer.
type   entails       (list formula) -> formula -> o.
type   entailst      (list formula) -> formula -> o.
infixr entails       7.
infixr entailst      7.

Gamma entails (constraint C) :-
  Gamma entailst (constraint C).
%  ( print "\nGamma is: ", write Gamma, print "\nC is: ", write C,
%    print "\nGamma entails C? [yes/no] ", read Ans, Ans = yes ).

nil entailst (constraint C) :- check C 0.

((constraint C')::Gamma) entailst (constraint C) :-
  (check C' _) => (Gamma entailst (constraint C)).

(H::Gamma) entailst (constraint C) :-
  Gamma entailst (constraint C).
