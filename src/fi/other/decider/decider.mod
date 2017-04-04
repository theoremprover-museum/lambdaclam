%
% My first attempt at building a PTL decider.
%
% cfr. Abadi/Manna, Nonclausal Deduction in First-Order Temporal Logic
%
%
% NOTES:
% -----
%
% Formulas are NOT implemented as lists of conjuncts (3.1), but rather as
% syntactic objects. Expansion to conjuncts is done only when requested
% (i.e., resolution).
%
% - does not yet implement resolution.
% - does not yet implement full induction.
% 
% this program is stupid as a goat.
%

module decider.

accumulate types, rules.

% ------------------------------------------
% ------------------------- the proof engine  
% ------------------------------------------

type step       formula -> formula -> o.
type prove      formula -> o.

step F G :- rule R, R F G, (expl R S, print S).

% these embed the recursive-calls rule.

step (box F) (box G) &
step (circle F) (circle G) &
step (diamond F) (diamond G) &
step (neg F) (neg G) :-
        step F G.

step (and F G) (and H I) &
step (or F G) (or H I) &
step (imp F G) (imp H I) :-
        step F H; step G I.

prove ff.
prove F :- step F G,
        (print " yields:      ", term_to_string G S, print S, print "\n"),
        prove G.


%
% templates (will someday Terzo have a DECENT user interface?)
%
% #set path "/hame/claudio/lprolog/decider/ " path.
% #load "/hame/claudio/lprolog/decider/load".
%
% to be proved:
%
% #query decider prove (and (box (and (neg (p "p")) (neg (p "q")))) (or (diamond (p "p")) (diamond (p "q")))).
%
