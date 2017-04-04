/* 

File: thy_compiler.mod
Description: On-the-fly theory inclusion
Last Modified: May 2002

*/

module thy_compiler.

accumulate envparser.


type mytest syn_decl -> o.

mytest (type_decl X) :- print "My test.\n".

type  all_pred  (X -> o) -> (list X) -> o.

all_pred P nil.
all_pred P (H::T) :- P H, all_pred P T.

type sublist (list X) -> (list X) -> o.

sublist Xs Ys :- all_pred (X\ (ly_member X Ys)) Xs.


/* Two stages: parsefile reads concrete syntax from a file and generates
   abstract syntax in the form of a theory name, logic name, and list of
   syn_decl, all wrapped in a theory_decl_gs; this is then converted by
   import_lclam_decls into a list of true assertions of type o. These are
   returned by use_thy.
*/ 


execute_command (add_theory Theory) Loop :-
	print "Trying ...",
	use_thy Theory As,
	assert_all As (pprint_string "Done", Loop).


use_thy S As :-
	parsefile S (theory_decl_gs Th Lo Ds),
	print "Successfully parsed\n",
	print "Checking well-formedness...\n",
	well_formed_decls Ds,
	print "Theory is well-formed\n",
	print "Importing lclam declarations...\n", !,
	import_lclam_decls Th Lo Ds As,
	print "Successfully processed\n".


type accum_assertions  (syn_decl -> (list o) -> o) -> (list syn_decl) -> (list o) -> o.

accum_assertions P nil nil.
accum_assertions P (D::Ds) As :-
	P D MoreAs, accum_assertions P Ds AsSoFar,
	append MoreAs AsSoFar As.



/*
Check that the declarations of types, terms, axioms, inferences and
conjectures are well-formed. 
*/

type well_formed_decls (list syn_decl) -> o.

well_formed_decls [].

/*
well_formed_decls (D::Ds) :-
	well_formed_decl D, 
%	(decl2binding D B),
	D = (type_decl S),
	((new_type S) => well_formed_decls Ds).
*/

well_formed_decls ((type_decl S)::Ds) :-
	well_formed_decl (type_decl S),
	((new_type S) => well_formed_decls Ds).

well_formed_decls ((typed_const_decl S T)::Ds) :-
	well_formed_decl (typed_const_decl S T),
	((new_const S T) => well_formed_decls Ds).

well_formed_decls ((axiom_decl S H C)::Ds) :-
	well_formed_decl (axiom_decl S H C),
	((new_axiom S) => well_formed_decls Ds).

well_formed_decls ((inference_decl S Hyps H2 C2)::Ds) :-
	well_formed_decl (inference_decl S Hyps H2 C2),
	((new_inference S) => well_formed_decls Ds).

well_formed_decls ((conj_decl S H C)::Ds) :-
	well_formed_decl (conj_decl S H C),
	((new_conjecture S) => well_formed_decls Ds).

well_formed_decls ((pred_decl S Ts)::Ds) :-
	well_formed_decl (pred_decl S Ts),
	((new_predicate S Ts) => well_formed_decls Ds).


well_formed_decls ((define S Te Ty)::Ds) :-
	well_formed_decl (define S Te Ty),
	((new_definition S Te Ty) => well_formed_decls Ds).


%well_formed_decls Ds :- well_formed_decls_in_env [] Ds.

%type well_formed_decls_in_env env -> (list syn_decl) -> o.

%well_formed_decls_in_env _ [].
%well_formed_decls_in_env E (D::Ds) :- decl2binding D B,
%				      B => well_formed_decls_in_env


type well_formed_decl syn_decl -> o.

well_formed_decl (type_decl S) :-
	not (new_type S),
	M is "Type " ^ S ^ "\n",
	print M.

well_formed_decl (typed_const_decl S T) :-
	not (new_const S _),
	well_formed_type T,
	M is "Constant " ^ S ^ "\n",
	print M.

well_formed_decl (axiom_decl S H C) :-
	not (new_axiom S),
	ly_append H [C] Ps,
	well_formed_assertions Ps,
	M is "Axiom " ^ S ^ "\n",
	print M.

well_formed_decl (conj_decl S H C) :-
	not (new_conjecture S),
	ly_append H [C] Ps,
	well_formed_assertions Ps,
	M is "Conjecture " ^ S ^ "\n",
	print M.

well_formed_decl (pred_decl S Ts) :-
	not (new_predicate S _),
	all_pred well_formed_type Ts,
	M is "Predicate " ^ S ^ "\n",
	print M.

well_formed_decl (define S Ty universe) :-
	not (new_type S),
	well_formed_type Ty,
	M is "Define type " ^ S ^ "\n",
	print M.

well_formed_decl (define S Te Ty) :-
	not (new_const S _),
	not (new_definition S _ _),
%	well_typed_term Te Ty,
	M is "Definition " ^ S ^ "\n",
	print M.


type  group_assertions  (pairty (list osyn) osyn) -> (list osyn) -> o.

group_assertions (pair Hyps Conc) Ass :- ly_append Hyps [Conc] Ass.

well_formed_decl (inference_decl S Hyps H2 C2) :-
	not (new_inference S),
	map_pred2 group_assertions Hyps Ass,
	all_pred well_formed_assertions Ass,
	ly_append H2 [C2] Ps2,
	well_formed_assertions Ps2,
	M is "Inference " ^ S ^ "\n",
	print M.


type well_formed_assertions (list osyn) -> o.

well_formed_assertions [].
well_formed_assertions ((otype_of (user_object X) T)::Ps) :-
	!,
	well_formed_type T,
	(new_const X T) => well_formed_assertions Ps.

% We assume that well-formedness does not depend on truth.

well_formed_assertions (P::Ps) :-
	well_formed_assertion P,
	well_formed_assertions Ps.

type well_formed_assertion osyn -> o.

well_formed_assertion (user_object P).

well_formed_assertion trueP.
well_formed_assertion falseP.

well_formed_assertion (app Op (tuple [P, Q])) :-
	ly_member Op [and, or, imp],
	well_formed_assertion P,
	well_formed_assertion Q.

well_formed_assertion (app eq (tuple [X, Y])) :-
	well_typed_term X T,
	well_typed_term Y T.

% predications

well_formed_assertion (app (user_object F) X) :-
	new_predicate F [T],
	well_typed_term X T.

well_formed_assertion (app forall (tuple [T, abs P])) :-
	well_formed_type T,
	pi X \ (new_const X T) => well_formed_assertion (P (user_object X)). 

well_formed_assertion (app exists (tuple [T, abs P])) :-
	well_formed_type T,
	pi X \ (new_const X T) => well_formed_assertion (P (user_object X)). 

% Backtracking on well_typed_term can lead to stack overflow.
% eg. well_typed_term X nat

type well_typed_term osyn -> osyn -> o.

well_typed_term trueP bool.

well_typed_term (user_object I) T :- new_const I T.

well_typed_term (app X Y) U :-
	well_typed_term X (T arrow U),
	well_typed_term Y T.

well_typed_term (ty_abs T L) (T arrow U) :-
	well_formed_type T,
	pi X \ (new_const X T) => well_typed_term (L (user_object X)) U.


type well_formed_type osyn -> o.

well_formed_type nat.
well_formed_type bool.
well_formed_type (X arrow Y) :-
	well_formed_type X,
	well_formed_type Y.

well_formed_type (tuple_type Ts) :-
	all_pred well_formed_type Ts.

well_formed_type (user_object S) :- new_type S.


type import_lclam_decls  string -> string -> (list syn_decl) -> (list o) -> o.

import_lclam_decls Th0 Lo Ds As:- 
	lower Th0 Th,       % convert theory name to lower case
	ThTitle is "Theory " ^ Th ^"\n", 
%	print ThTitle,
	accum_assertions (import_one_decl Th Lo) Ds As.


% decapitalise first letter of string if necessary

type lower string -> string -> o.

lower "" "" :- !.

lower S S2 :-
	N is size S,
	H is string_to_int S,
	T is substring S 1 (N - 1),
	((H < 90, H2 is (H + 32));(H > 96, H2 is H)),
	H3 is chr H2,
	S2 is H3 ^ T.

%type import_lclam_decls  string -> string -> (list syn_decl) -> (list assertion) -> o.

%import_lclam_decls Th Lo Ds As:- 


type import_one_decl  string -> string -> syn_decl -> (list o) -> o.

import_one_decl Th Lo (type_decl S) ((has_otype (user_theory Th) (user_object S) universe)::nil).


import_one_decl Th Lo (typed_const_decl S T)
	((has_otype (user_theory Th) (user_object S) T)::nil) :-
	print "Typed constant!\n".



type generic  (list osyn) -> osyn -> o.
/* should just succeed once */
generic AxHyps AxConc :- member (user_object G) (AxConc::AxHyps).

type  axiom2method  (list osyn) -> osyn -> (list osyn) -> osyn -> o.


axiom2method AxHyps AxConc MethHyps MethConc :-
	ly_filter (P \ not (P = (user_object G))) AxHyps MethHyps.
% should bind vars, so that user_object "P" becomes a var, etc.
% Just leave it unbound here
	
/*

import_one_decl "Nsa" "arithmetic" (axiom_decl "false_e" (user_object "G1" :: falseP :: user_object "G2" :: nil) (user_object "P")) A.

(axiom_decl S AxHyps AxConc) = (axiom_decl "false_e" (user_object "G1" :: falseP :: user_object "G2" :: nil) (user_object "P")),
generic AxHyps AxConc.


*/


import_one_decl Th Lo (axiom_decl S AxHyps AxConc) (A::nil) :-
	generic AxHyps AxConc,
	axiom2method AxHyps AxConc MethHyps MethConc, %MethConc not bound
	(	(MethHyps = nil, MethHyps2 = true)
	;
		(Pre = (sublist (MethHyps) H))
	),
	In = (seqGoal (H >>> MethConc)),
	A = (atomic (user_theory Th) (user_method S) In Pre true trueGoal notacticyet),
	print "Generic axiom!\n".



/*

import_one_decl "Nsa" "arithmetic"
(axiom_decl "qs" nil (app imp (tuple (app forall (tuple (nat :: abs (W1\ app exists (tuple (nat :: abs (W2\ app eq (tuple (W1 :: W2 :: nil))) :: nil))) :: nil)) :: trueP :: nil)))) A.


Sols = rewrite_osyns trueP (app imp (tuple (app forall (tuple (nat :: abs (W1\ app exists (tuple (nat :: abs (W2\ app eq (tuple (W1 :: W2 :: nil))) :: nil))) :: nil)) :: trueP :: nil))) trueP :: rewrite_osyns trueP trueP (app forall (tuple (nat :: abs (W1\ app exists (tuple (nat :: abs (W2\ app eq (tuple (W1 :: W2 :: nil))) :: nil))) :: nil))) :: nil

*/

/* Returns a list of assertions */

import_one_decl Th Lo (axiom_decl S H Conc) As :-
	not (generic H Conc),
	allsols (X \ (sigma C \ sigma L \ sigma R \ (osyn2rewrite2 H Conc C L R, X = rewrite_osyns C L R))) Sols,
	foldr_pred (print_CLR2 Th S) (mypair 1 nil) Sols (mypair _ As),
	print "Non-generic axiom!\n".



type print_CLR2 string -> string -> rewrite_syn -> myprod -> myprod -> o.

print_CLR2 Th S (rewrite_osyns C L R) (mypair N SoFar) (mypair M (A::SoFar)) :-
	N_string is int_to_string N,
	AxName is S ^ N_string,
	A = (axiom (user_theory Th) (user_rewrite AxName) ltor C L R), 
	M is N + 1.

type is_context_var osyn -> o.

is_context_var (user_object "G").
is_context_var (user_object "G'").

type not_context_var osyn -> o.

not_context_var X :- not (is_context_var X).

/*

import_one_decl "Nsa" "arithmetic"
(inference_decl "inf1" (pair (trueP :: nil) falseP :: nil) (trueP :: otype_of (user_object "x") nat :: nil) (app eq (tuple (user_object "x" :: user_object "x" :: nil)))) A.


import_one_decl  "Nsa" "arithmetic" (inference_decl "or_l" (pair (user_object "G" :: user_object "A" :: nil) (user_object "P") :: pair (user_object "G" :: user_object "B" :: nil) (user_object "P") :: nil) (user_object "G" :: app or (tuple (user_object "A" :: user_object "B" :: nil)) :: nil) (user_object "P")) A.

import_one_decl "Nsa" "arithmetic"
(inference_decl "and_l" (pair (user_object "G1" :: user_object "A" :: user_object "B" :: user_object "G2" :: nil) (user_object "P") :: nil) (user_object "G1" :: app and (tuple (user_object "A" :: user_object "B" :: nil)) :: user_object "G2" :: nil) (user_object "P")) A.

*/


import_one_decl Th Lo (inference_decl S Hyps Ants Succ) (A::nil) :- 
	print "Inference!\n",
	ly_filter (P \ not (P = (user_object G))) Ants In_ants,
	map_pred2 getAnts Hyps HypContexts,
	map_pred2 getSucc Hyps HypSuccs,
	map_pred2 (ly_filter not_context_var) HypContexts Out_hyps,
	map_pred2 tuplify Out_hyps Out_hyps_tuples,
	abstract3 (tuple [Succ, (tuple In_ants), (tuple Out_hyps_tuples), (tuple HypSuccs)]) N Z,
	newvars N LogVars,
	newvars 100 Vars,
	Vars = H::MoreVars,
%	nth Vars 1 H, 
	apply LogVars Z	(tuple [Succ2, (tuple In_ants2), (tuple Out_hyps_tuples2), (tuple HypSuccs2)]),
	map_pred2 untuplify Out_hyps_tuples2 Out_hyps2,
	(	(In_ants2 = nil, Pre0 = true)
		;
		(Pre0 =(sublist In_ants2 H))
	), /* put result of this foldr_pred in Pre0 and prefix to Pre */
	foldr_pred (replace_hyps2 H MoreVars In_ants2) (polypair 1 Pre0) Out_hyps2 (polypair _ Pre),
/* Can be several outgoals */
	HypSuccs2 = HypSucc::HypSuccs1,
	nth MoreVars 1 H1 _,
	OG1 = (seqGoal (H1 >>> HypSucc)),
	foldr_pred (mkOutGoal MoreVars) (polypair 2 OG1) HypSuccs1 (polypair _ Out),
	A = (atomic (user_theory Th) (user_method S) (seqGoal (H >>> Succ2)) Pre true Out notacticyet).



type  mkOutGoal (list X) -> osyn -> (polyprod int goal) -> (polyprod int goal) -> o.

mkOutGoal Vars Succ (polypair N SoFar) (polypair M After) :-
	M is N + 1,
	nth Vars N HN _,
	After = SoFar ** (seqGoal (HN >>> Succ)).


type replace_hyps2 X -> (list X) -> list osyn -> list osyn -> 
	(polyprod int o) -> (polyprod int o) -> o.


type dummy osyn.

replace_hyps2 H Vars In_ants Ants_n (polypair N PreSoFar) (polypair M PreNow) :-
	M is N + 1,
%	nth Vars 1 H _, /* antecedent of In */
	nth Vars N Hyp_n _,
/*	Hyp_n = (H ^ (int_to_string N), */
	((In_ants = Ants_n, /* eg. both are nil */
	PreNow = (PreSoFar, H = Hyp_n),
	!)
	;
	(In_ants = [In_ant], not (In_ant = dummy),
	PreNow = (PreSoFar, replace_in_hyps H In_ant Ants_n Hyp_n)
	)
	;
	PreNow = PreSoFar). /* Was true before */


/*

import_one_decl  "Nsa" "arithmetic"
(conj_decl "conj1" (otype_of (user_object "x") nat :: nil) (app forall (tuple (nat :: abs (W1\ app eq (tuple (user_object "x" :: W1 :: nil))) :: nil)))) As.

*/

import_one_decl Th Lo (conj_decl S H C) 
		((top_goal (user_theory Th) (user_query S) H C)::nil) :-
	print "Conjecture!\n".

import_one_decl Th Lo (pred_decl S Ts) As :- 
	print "Predicate!\n".

/*

import_one_decl  "Nsa" "arithmetic"
(define "real_pair" (tuple_type (user_object "real" :: user_object "real" :: nil)) universe) As.

*/

import_one_decl Th Lo (define S Te Ty) 
		((definition (user_theory Th) (user_rewrite S) trueP Te Ty)::nil) :- 
	print "Definition!\n".


type tuplify (list osyn) -> osyn -> o.

tuplify Xs (tuple Xs).


type untuplify osyn -> (list osyn) -> o.

untuplify (tuple Xs) Xs.


type abstract2  (list osyn) -> osyn -> osyn -> o.

abstract2 nil R R.
abstract2 ((user_object X)::Vars) R R2 :-
	formlam X R R3,
	abstract2 Vars (abs R3) R2.

type abstract3 osyn -> int -> osyn -> o.

abstract3 X N Y :-
	getVars X Vars,
	ly_length Vars N,
	abstract2 Vars X Y.

type getVars osyn -> (list osyn) -> o.

getVars X Vars :-
	allsols (U \ (sigma Y \ (U = user_object Y, subterm U X))) Vars.

type subterm osyn -> osyn -> o.

subterm X X.
subterm X (app A B):- subterm X A.
subterm X (app A B):- subterm X B.
subterm X (tuple (H::T)):- subterm X H.
subterm X (tuple (H::T)):- subterm X (tuple T).
subterm X (abs F):- pi x \ (subterm X (F x)).


type  getAnts  (pairty (list osyn) osyn) -> (list osyn) -> o.

getAnts (pair Ants Succ) Ants.


type  getSucc  (pairty (list osyn) osyn) -> osyn -> o.

getSucc (pair Ants Succ) Succ.



type osyn2rewrite2  (list osyn) -> osyn -> osyn -> osyn -> osyn -> o.

osyn2rewrite2 Hyps Conc C L R :-
split_hyps Hyps Vars Pres,
osyn2rewrite Conc C2 L2 R2,
combine Pres C2 L2 R2 Cs3 L3 R3,
conjoin Cs3 C3,
abstract2 Vars (tuple [C3, L3, R3]) Z,
ly_length Vars N,
newvars N LogVars,
apply LogVars Z (tuple [C, L, R]).


type split_hyps  (list osyn) -> (list osyn) -> (list osyn) -> o.

split_hyps ((otype_of (user_object X) T)::Hyps) ((user_object X)::Vars) Pres
:- !, split_hyps Hyps Vars Pres.

split_hyps (P::Hyps) Vars (P::Pres)
:- split_hyps Hyps Vars Pres.

split_hyps nil nil nil.

type  osyn2rewrite  osyn -> osyn -> osyn -> osyn -> o.

osyn2rewrite (app imp (tuple [C, app eq (tuple [L,R])])) C L R.
osyn2rewrite (app imp (tuple [C, app eq (tuple [R,L])])) C L R.
osyn2rewrite (app imp (tuple [C, app imp (tuple [R,L])])) C L R.
osyn2rewrite (app eq (tuple [L,R])) trueP L R.
osyn2rewrite (app eq (tuple [R,L])) trueP L R.
osyn2rewrite (app imp (tuple [R,L])) trueP L R.
osyn2rewrite X trueP X trueP.


type combine  (list osyn) -> osyn -> osyn -> osyn -> (list osyn) -> osyn -> osyn -> o.

combine Pres C2 L2 R2 Cs L2 R2 :-
	ly_append Pres [C2] Cs2,
	strip_true Cs2 Cs.

type strip_true  (list osyn) -> (list osyn) -> o.

strip_true Ps Qs :-
	ly_filter (P\ (not (P = trueP))) Ps Qs0,
	((Qs0 = nil, Qs = [trueP])
	;
	(not (Qs0 = nil), Qs = Qs0)).

type  conjoin  (list osyn) -> osyn -> o.

conjoin [P] P.
conjoin (P::Ps) Q :- conjoin Ps Q2, Q = (app and (tuple [P, Q2])).



type abstract  (list osyn) -> osyn -> osyn -> o.

abstract nil R R.
abstract ((user_object X)::Vars) R R2 :-
	formlam X R R3,
	newvar Y,
	abstract Vars (R3 Y) R2.

type  newvar osyn -> o.

newvar X.

type newvars int -> (list X) -> o.

newvars 0 nil :- !.
newvars N (V::Vars) :- M is (N - 1), newvars M Vars.


type apply (list X) -> osyn -> osyn -> o.

apply nil X X.
apply (V::Vars) (abs L) X :- apply Vars (L V) X.


type foldr_pred (A -> B -> B -> o) -> B -> list A -> B -> o.

foldr_pred P X nil X.
foldr_pred P X (W :: L) Z :- foldr_pred P X L Y, P W Y Z.

type allsols  (A -> o) -> list A -> o.
local alls    (A -> o) -> list A -> list A -> o.

allsols Prop L :- alls Prop L nil.

alls Prop L T :- Prop H, not (ly_member H T), alls Prop L (H::T), !.
%alls Prop L T :- Prop H, ly_member H T, alls Prop L T, !.
alls Prop L L.



sublist Xs Ys :- all_pred (X\ (ly_member X Ys)) Xs.


type  all_pred  (X -> o) -> (list X) -> o.

all_pred P nil.
all_pred P (H::T) :- P H, all_pred P T.


end