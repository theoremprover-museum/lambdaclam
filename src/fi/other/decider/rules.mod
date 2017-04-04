%
% PTL decider
%
% rules definitions.
%

module rules.

accumulate types, decider.

% ------------------------------------------
% ---------------------------- preliminaries
% ------------------------------------------

type append     list A -> list A -> list A -> o.
type member     A -> list A -> o.
type del        A -> list A -> list A -> o.
type cmn        list A -> list A -> A -> o.

member X (X::L).
member X (_::L) :- member X L.

append nil K K.
append (X::L) K (X::M) :- append L K M.

del X (X::L) L.
del X (Y::L) M :- del X L M.

cmn (F::L1) L2 F :- member F L2.
cmn (_::L1) L2 F :- cmn L1 L2 F.

% ------------------------------------------
% -------------------------------- conjuncts
% ------------------------------------------

type conj       formula -> list A -> o.

conj (and F G) L :- conj F L1, conj G L2, append ((and F G)::L1) L2 L, !.
conj F L :- append (F::nil) nil L.

% ------------------------------------------
% ------------------------------------ rules
% ------------------------------------------

type rule       (formula -> formula -> o) -> o.

% ------------------------------------ simplification rules (3.2.1)
% we discard F(i) once we've derived F(i+1)

% ***************** on boolean operators

type fs1, fs2, fs3 formula -> formula -> o.
rule fs1.
rule fs2.
rule fs3.
expl fs1 "false-or-something".
expl fs2 "something-or-false".
expl fs3 "something-and-false".
fs1 (or ff G) G.
fs2 (or G ff) G.
fs3 F ff :-
        conj F L, member ff L.

% ***************** on modal operators

type fs4, fs5, fs6 formula -> formula -> o.
rule fs4.
rule fs5.
rule fs6.
expl fs4 "box-false".
expl fs5 "diamond-false".
expl fs6 "circle-false".
fs4 (box ff) ff.
fs5 (diamond ff) ff.
fs6 (circle ff) ff.

% ***************** weakening

type w formula -> formula -> o.
rule w.
expl w "weakening".
w F G :-
        conj F L, del F L M, member G M.

% ***************** negation rules

type n1, n2, n3, n4, n5, n6, n7, n8 formula -> formula -> o.
rule n1.
rule n2.
rule n3.
rule n4.
rule n5.
rule n6.
rule n7.
rule n8.
expl n1 "not-box".
expl n2 "not-diamond".
expl n3 "not-circle".
expl n4 "and-DeMorgan".
expl n5 "or-DeMorgan".
expl n6 "not-not".
expl n7 "not-tt".
expl n8 "not-ff".
n1 (neg (box F)) (diamond (neg F)).
n2 (neg (diamond F)) (box (neg F)).
n3 (neg (circle F)) (circle (neg F)).
n4 (neg (and F G)) (or (neg F) (neg G)).
n5 (neg (or F G)) (and (neg F) (neg G)).
n6 (neg (neg F)) F.
n7 (neg tt) ff.
n8 (neg ff) tt.

% ------------------------------------ deduction rules (3.2.2 -- 3.2.6)
% we add F(i+1) to the conjuncts of F(i)

% ***************** distribution rule (3.2.2)

type aod formula -> formula -> o.
rule aod.
expl aod "and-or-distribution".
aod F (and F (or (and U V1) (and U V2))) :-
        conj F L, member U L, member (or V1 V2) L.

% ***************** resolution rule (3.2.3)

type res formula -> formula -> o.
rule res.
expl res "resolution".
res (and A B) (and (and A B) (or A1 B1)) :-
        subf L1 A, subf L2 B, cmn L1 L2 F,
        subst A A1 F tt, subst B B1 F ff.

% build list of subformulas of a formula.
type subf list formula -> formula -> o.
subf L (p S) :- append ((p S)::nil) nil L.
subf L (box F) :- subf L1 F, append ((box F)::nil) L1 L.
subf L (circle F) :- subf L1 F, append ((circle F)::nil) L1 L.
subf L (diamond F) :- subf L1 F, append ((diamond F)::nil) L1 L.
subf L (neg F) :- subf L1 F, append ((neg F)::nil) L1 L.
subf L (imp A B) :- subf L1 A, subf L2 B, append ((imp A B)::L1) L2 L.
subf L (and A B) :- subf L1 A, subf L2 B, append ((and A B)::L1) L2 L.
subf L (or A B) :- subf L1 A, subf L2 B, append ((or A B)::L1) L2 L.

% substitute every occurrence of F in A with G, obtaining B.
type subst formula -> formula -> formula -> formula -> o.
subst (p _) _ _ _, !.
subst (box F) (box G) F G.
subst (circle F) (circle G) F G.
subst (diamond F) (diamond G) F G.
subst (neg F) (neg G) F G :- !.
subst (neg X) (neg Y) F G :- subst X Y F G.
subst (imp F X) (imp G Y) F G :- !, subst X Y F G.
subst (imp X F) (imp Y G) F G :- !, subst X Y F G.
subst (and F X) (and G Y) F G :- !, subst X Y F G.
subst (and X F) (and Y G) F G :- !, subst X Y F G.
subst (or F X) (or G Y) F G :- !, subst X Y F G.
subst (or X F) (or Y G) F G :- !, subst X Y F G.

% ***************** modality rules (3.2.4)

type ccr, br, dr, bbr, bdr, ddr, bcr, dcr formula -> formula -> o.
rule ccr.
rule br.
rule dr.
rule bbr.
rule bdr.
rule ddr.
rule bcr.
rule dcr.
expl ccr "circle-circle-rule".
expl br  "box-rule".
expl dr  "diamond-rule".
expl bbr "box-box-rule".
expl bdr "box-diamond-rule".
expl ddr "diamond-diamond-rule".
expl bcr "box-circle-rule".
expl dcr "diamond-circle-rule".
ccr F (and F (circle (and A B))) :-
        conj F L, member (circle A) L, member (circle B) L.
br (box F) (and (box F) (circle (box F))).
dr (diamond F) (or (diamond F) (circle (diamond F))).
bbr F (and F (box (and (box A) B))) :-
        conj F L, member (box A) L, member (box B) L.
bdr F (and F (diamond (and (box A) B))) :-
        conj F L, member (box A) L, member (diamond B) L.
ddr F (and F (or (diamond (and A (diamond B))) (diamond (and (diamond A) B)))) :-
        conj F L, member (diamond A) L, member (diamond B) L.
bcr F (and F (circle (and (box A) B))) :-
        conj F L, member (box A) L, member (circle B) L.
dcr F (and F (or A (circle (and (diamond A) B)))) :-
        conj F L, member (diamond A) L, member (circle B) L.

% ***************** restricted induction rule (3.2.5)

type ind formula -> formula -> o.
rule ind.
expl ind "induction".
ind F (and F (diamond (and (neg A) (circle A)))) :-
        conj F L, member (neg A) L, member (diamond A) L.

% ***************** full induction rule (3.2.5)
% ---> use at your own risk.

type find formula -> formula -> o.
rule find.
expl find "full-induction".
find F (and F (diamond ( and (neg U) (circle (and U (neg W)))))) :-
        conj F L, member W L, member (circle U) L,
        prove (neg (and W U)).
