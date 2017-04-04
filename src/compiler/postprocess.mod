/*

This code calls envparser to parse a theory file into 
(theory_decl_gs Theory Logic Decls), checks its well-formedness, and then
outputs it as a lambda-clam readable theory file.

*/

module postprocess.
accumulate envparser.
accumulate logic_eq_constants.

%% Predicate to get thing to compile
local cc_pred osyn -> o.
cc_pred X.

type new_type string -> o.
type new_const string -> osyn -> o.
%type new_axiom string -> (list osyn) -> osyn -> o.
%type new_inference string -> (list osyn) -> osyn -> (list osyn) -> osyn -> o.

type decl2binding syn_decl -> o -> o.

decl2binding (type_decl S) (new_type S).

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
	member Op [and, or, imp],
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


type well_formed_sequent osyn -> o.


%type droll int -> o.
%droll X :- (X = 2) => not (X = 2).

%type droll (list string) -> o.

%droll (S::SS) :- !,(new_type "t") => (droll SS).
%droll SS :- not (new_type _).


type process_file string -> o.

process_file S :-
	parsefile S (theory_decl_gs Th Lo Ds),
	print "Successfully parsed\n",
	print "Checking well-formedness...\n",
	well_formed_decls Ds,
	print "Theory is well-formed\n",
	print "Outputing lclam theory files...\n",
	generate-lclam Th Lo Ds,
	generate-xml Th Lo Ds,
	print "Successfully processed\n".

% generate-lclam theory-name logic-used decls

type generate-lclam string -> string -> (list syn_decl) -> o.

% converts theory name to lower case

generate-lclam Th0 Lo Ds :-
	lower Th0 Th,
	Sigfile is Th ^ "theory.sig",
	open_out Sigfile SS,
	SigPre is "sig " ^ Th ^ "theory.\naccum_sig " ^ Lo ^ ".\n\ntype " ^ Th ^ " theory.\n",
	output SS SigPre,
	output SS "type all_pred (X -> o) -> (list X) -> o.\n",
	output SS "type sublist (list X) -> (list X) -> o.\n",
	Modfile is Th ^ "theory.mod",
	open_out Modfile OS,
	ModPre is "module " ^ Th ^ "theory.\naccumulate " ^ Lo ^ ".\n\n",
	output OS ModPre,
	output OS "all_pred P nil.\nall_pred P (H::T) :- P H, all_pred P T.\n",
	output OS "sublist Xs Ys :- all_pred (X\\ (member X Ys)) Xs.\n\n",
%	pi D \ (member D Ds) => (decl2lclam OS Th Lo D),
%	foldr_pred (decl2lclam OS Th Lo) true Ds,
	all_pred (decl2lclam SS OS Th Lo) Ds,
	output SS "end\n",	
	output OS "end\n",
	close_out SS,
	close_out OS,
	M is "Created " ^ Th ^ "theory files\n",
	print M.

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

type decl2lclam  out_stream -> out_stream -> string -> string -> syn_decl -> o.

decl2lclam SS OS Th Lo (type_decl S) :-
	Typedecl is "type " ^ S ^ " osyn.\n",
	output SS Typedecl,
	Typekind is "has_otype " ^ Th ^ " " ^ S ^ " universe.\n",
	output OS Typekind.

decl2lclam SS OS Th Lo (typed_const_decl S T) :-
	Decl is "type " ^ S ^ " osyn.\n",
	output SS Decl,
	Defn is "has_otype " ^ Th ^ " " ^ S ^ " ",
	output OS Defn,
	print_bracketed_term OS T,
	output OS ".\n".

kind rewrite_syn type.
type rewrite_osyns osyn -> osyn -> osyn -> rewrite_syn.

type generic  (list osyn) -> osyn -> o.

generic AxHyps AxConc :- member (user_object G) (AxConc::AxHyps).

type  axiom2method  (list osyn) -> osyn -> (list osyn) -> osyn -> o.


axiom2method AxHyps AxConc MethHyps MethConc :-
	ly_filter (P \ not (P = (user_object G))) AxHyps MethHyps.
% should bind vars, so that user_object "P" becomes a var, etc.
% Just leave it unbound here


decl2lclam SS OS Th Lo (axiom_decl S AxHyps AxConc) :-
	generic AxHyps AxConc,
	axiom2method AxHyps AxConc MethHyps MethConc, %MethConc not bound
	Decl is "type " ^ S ^ " meth.\n",
	output SS Decl,
	Title is "atomic " ^ Th ^ " " ^ S ^ "\n",
	output OS Title,
	In is "\t(seqGoal (H >>> ",
	output OS In,
	print_bracketed_term OS MethConc,
	output OS "))\n",
	(	(MethHyps = nil,
		output OS "\ttrue\n")
		;
		(output OS "\t(sublist (",
		printterm OS MethHyps,
		output OS ") H)\n")
	),
	output OS "\ttrue\n\ttrueGoal\n\tnotacticyet.\n\n".


decl2lclam SS OS Th Lo (axiom_decl S H Conc) :-
	not (generic H Conc),
	allsols (X \ (sigma C \ sigma L \ sigma R \ (osyn2rewrite2 H Conc C L R, X = rewrite_osyns C L R))) Sols,
	
%	Decl is "type " ^ S ^ " rewrite_rule.\n",
%	output SS Decl,
%	Defn is "axiom " ^ Th ^ " " ^ S ^ " ltor ",
%	output OS Defn,

	foldr_pred (print_CLR SS OS Th S) 1 Sols _.

%	print_bracketed_term OS C, output OS " ",
%	print_bracketed_term OS L, output OS " ",
%	print_bracketed_term OS R,

%	output OS ".\n".

type print_CLR out_stream -> out_stream -> string -> string -> rewrite_syn -> 
int -> int -> o.

print_CLR SS OS Th S (rewrite_osyns C L R) N M :-
	N_string is int_to_string N,
	Decl is "type " ^ S ^ N_string ^ " rewrite_rule.\n",
	output SS Decl,
	Defn is "axiom " ^ Th ^ " " ^ S ^ N_string ^ " ltor ",
	output OS Defn,
	print_bracketed_term OS C, output OS " ",
	print_bracketed_term OS L, output OS " ",
	print_bracketed_term OS R,
	output OS ".\n\n",
	M is N + 1.

type  getAnts  (pairty (list osyn) osyn) -> (list osyn) -> o.

getAnts (pair Ants Succ) Ants.


type  getSucc  (pairty (list osyn) osyn) -> osyn -> o.

getSucc (pair Ants Succ) Succ.


type is_context_var osyn -> o.

is_context_var (user_object "G").
is_context_var (user_object "G'").

type not_context_var osyn -> o.

not_context_var X :- not (is_context_var X).


decl2lclam SS OS Th Lo (inference_decl S Hyps Ants Succ) :-
	Decl is "type " ^ S ^ " meth.\n",
	output SS Decl,
	Title is "atomic " ^ Th ^ " " ^ S ^ "\n",
	output OS Title,
	ly_filter (P \ not (P = (user_object G))) Ants In_ants,
%	[In_ant] = In_ants,
	map_pred2 getAnts Hyps HypContexts,
	map_pred2 getSucc Hyps HypSuccs,
	map_pred2 (ly_filter not_context_var) HypContexts Out_hyps,
	map_pred2 tuplify Out_hyps Out_hyps_tuples,
abstract3
   (tuple [Succ, (tuple In_ants), (tuple Out_hyps_tuples), (tuple HypSuccs)]) N Z,
newvars N LogVars,
apply LogVars Z
   (tuple [Succ2, (tuple In_ants2), (tuple Out_hyps_tuples2), (tuple HypSuccs2)]),
	map_pred2 untuplify Out_hyps_tuples2 Out_hyps2,
	In is "\t(seqGoal (H >>> ",
	output OS In,
	print_bracketed_term OS Succ2, /* For axioms, we computed MethConc */
	output OS "))\n",
	(	(In_ants2 = nil, output OS "\t(true")
		;
		(output OS "\t(sublist (",
		printterm OS In_ants2,  /* For axioms, we computed MethHyps */
		output OS ") H")
	),
%	output OS "\t(",
	foldr_pred (replace_hyps2 OS In_ants2) 1 Out_hyps2 _,
%	all_pred (replace_hyps OS In_ants) Out_hyps,
	output OS ")\n",
	output OS "\ttrue\n", /* effects */
	HypSuccs2 = HypSucc::HypSuccs1,
	OG1 is "\t(seqGoal (H1 >>> ",
	output OS OG1,
	printterm OS HypSucc,
	output OS ")",
	foldr_pred (mkOutGoal OS) 2 HypSuccs1 _,
	output OS ")\n\tnotacticyet.\n\n".

type tuplify (list osyn) -> osyn -> o.

tuplify Xs (tuple Xs).

type untuplify osyn -> (list osyn) -> o.

untuplify (tuple Xs) Xs.


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



type  mkOutGoal out_stream -> osyn -> int -> int -> o.

mkOutGoal OS Succ N M :-
	M is N + 1,
	S is " ** seqGoal (H" ^ (int_to_string N) ^ " >>> ",
	output OS S,
	printterm OS Succ,
	output OS ")".


type  replace_hyps2  out_stream -> list osyn -> list osyn -> int -> int -> o.

replace_hyps2 OS In_ants Ants_n N M :-
	M is N + 1,
	Hyp_n is " H" ^ (int_to_string N),
	((In_ants = Ants_n, /* eg. both are nil */
	Cond is ", H = " ^ Hyp_n,
	output OS Cond,
	!)
	;
	(In_ants = [In_ant], not (In_ant = dummy),
	output OS ", replace_in_hyps H ",
	print_bracketed_term OS In_ant,
	output OS " ",
	print_bracketed_term OS Ants_n,
	output OS Hyp_n
	)
	;
	true).


type replace_hyps out_stream ->  (list osyn) -> (list osyn) -> o.

type dummy osyn.

replace_hyps OS In_ants Ants_n :-
	(In_ants = [In_ant], not (In_ant = dummy),
	output OS ", replace_in_hyps H ",
	print_bracketed_term OS In_ant,
	output OS " ",
	print_bracketed_term OS Ants_n,
	output OS " Hi, ")
	;
	true.


decl2lclam SS OS Th Lo (conj_decl S H C) :-
	Decl is "type " ^ S ^ " query.\n",
	output SS Decl,
	Defn is "top_goal " ^ Th ^ " " ^ S ^ " [",
	output OS Defn,
	print_hyps OS H,
	output OS "] ",
	print_bracketed_term OS C,
	output OS ".\n".



type print_hyps out_stream -> (list osyn) -> o.

print_hyps OS [].
print_hyps OS [H] :- print_bracketed_term OS H.
print_hyps OS (H1::H2::Hs) :-
	print_bracketed_term OS H1,
	output OS ", ",
	print_hyps OS (H2::Hs).

type print_hyp out_stream -> osyn -> o.

print_hyp OS P :- printterm OS P, output OS ", ".

% More bracketing than necessary

type print_bracketed_term out_stream -> X -> o.

print_bracketed_term OS P :- output OS "(", printterm OS P, output OS ")".

decl2lclam SS OS Th Lo (pred_decl S Ts).

/*

Definitions in lclam.

definition hol and1 trueP (app and (tuple [falseP, _])) falseP.

*/


decl2lclam SS OS Th Lo (define S Te Ty) :-
	Decl is "type " ^ S ^ " osyn.\ntype " ^ S ^ "0 rewrite_rule.\n",
	output SS Decl,
	Defn is "definition " ^ Th ^ " " ^ S ^ "0 trueP ",
	output OS Defn,
	print_bracketed_term OS Te,
	Defn2 is " " ^ S ^ ".\n",
	output OS Defn2.


/***************************************/


type generate-xml string -> string -> (list syn_decl) -> o.

generate-xml Th Lo Ds :-
	XMLfile is Th ^ "theory.xml",
	open_out XMLfile XS,
	output XS "<Theory>\n",
	all_pred (decl2xml XS Th Lo) Ds,
	output XS "</Theory>\n",
	close_out XS,
	M is "Created " ^ Th ^ " XML file\n",
	print M.

type decl2xml out_stream -> string -> string -> syn_decl -> o.

decl2xml XS Th Lo (type_decl S) :-
	Typedecl is "<Type>" ^ S ^ "</Type>\n",
	output XS Typedecl.

decl2xml XS Th Lo (typed_const_decl S T).
decl2xml XS Th Lo (axiom_decl S H Conc).
decl2xml XS Th Lo (inference_decl S Hyps H2 C2).
decl2xml XS Th Lo (conj_decl S H C).
decl2xml XS Th Lo (pred_decl S Ts).
decl2xml XS Th Lo (define S Te Ty).


/***************************************/


type balerno (list o) -> o -> o.
balerno L C :- print "Balerno", curry L C.

/*
type curry (list o) -> o -> o.

curry [] C :- C.
curry ((new_type S)::Hs) C :- 
	print "new type\n", 
	(new_type S) => (curry Hs C).
curry ((new_const S T)::Hs) C :- 
	print "new const\n",
	(new_const S T) => (curry Hs C).
curry ((new_axiom S Hs1 Cn)::Hs) C :- 
	print "new axiom\n",
	(new_axiom S Hs1 Cn) => (curry Hs C).
curry ((new_inference S H1 C1 H2 C2)::Hs) C :- 
	print "new inference\n",
	(new_inference S H1 C1 H2 C2) => (curry Hs C).
*/

%curry (H::Hs) C :- H => (curry Hs C).

%type curry2 (list o) -> o -> o -> o.

%curry2 [] C C.
%curry2 (H::Hs) C (H => X) :- curry2 Hs C X.

% dummy defn

type make_bindings theory -> (list syn_decl) -> (list o) -> o.

make_bindings Th [] [].
make_bindings Th (D::Ds) (B::Bs) :- make_binding Th D B, 
				    make_bindings Th Ds Bs.

/*
type make_binding theory -> syn_decl -> o -> o.

make_binding Th (type_decl S) (new_type S).
make_binding Th (typed_const_decl S T) (new_const S T).
make_binding Th (axiom_decl S Hs C) (new_axiom S Hs C).
make_binding Th (inference_decl S H1 C1 H2 C2) (new_inference S H1 C1 H2 C2).
*/

% This should probably be combined with well_formed_decls

type add_declarations theory -> (list syn_decl) -> o.

add_declarations Th [].
add_declarations Th (D::Ds) :-  add_declaration Th D, add_declarations Th Ds.

type add_declaration theory -> syn_decl -> o.

% This has to be at the right point in the lclam loop.

% We assume that the current theory Th is given by new_theory Th.
% Of the form user_theory "Theory Name".

% Type declarations

% is_otype?

%add_declaration Th (type_decl T) :- add_osyn Th (user_object T) universe.

% Typed constant declarations

%add_declaration Th (typed_const_decl C T) :- add_osyn Th (user_object C) T.

% Axiom declarations; here, we convert axioms into rewrites rather than
% methods.

% Must account for quantifiers

% This converts a single formula into a C, L and R.

osyn2rewrite (app imp (tuple [C, app eq (tuple [L,R])])) C L R.
osyn2rewrite (app imp (tuple [C, app eq (tuple [R,L])])) C L R.
osyn2rewrite (app imp (tuple [C, app imp (tuple [R,L])])) C L R.
osyn2rewrite (app eq (tuple [L,R])) trueP L R.
osyn2rewrite (app eq (tuple [R,L])) trueP L R.
osyn2rewrite (app imp (tuple [R,L])) trueP L R.
osyn2rewrite X trueP X trueP.

/*

axiom_decl "sch4" (otype_of (user_object "x") nat :: otype_of (user_object "y") nat :: app eq (tuple (user_object "x" :: user_object "y" :: nil)) :: nil) (app eq (tuple (user_object "y" :: user_object "x" :: nil)))

osyn2rewrite2 (otype_of (user_object "x") nat :: otype_of (user_object "y") nat :: app eq (tuple (user_object "x" :: user_object "y" :: nil)) :: nil) (app eq (tuple (user_object "y" :: user_object "x" :: nil))) C L R.


osyn2rewrite2 [otype_of (user_object "x") nat, otype_of (user_object "y") nat, app eq (tuple (user_object "x" :: user_object "y" :: nil))] (app eq (tuple [user_object "y", user_object "x"])) C L R.

*/

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

newvar X.

type newvars int -> (list X) -> o.

newvars 0 nil :- !.
newvars N (V::Vars) :- M is (N - 1), newvars M Vars.


type abstract2  (list osyn) -> osyn -> osyn -> o.

abstract2 nil R R.
abstract2 ((user_object X)::Vars) R R2 :-
	formlam X R R3,
	abstract2 Vars (abs R3) R2.


type apply (list X) -> osyn -> osyn -> o.

apply nil X X.
apply (V::Vars) (abs L) X :- apply Vars (L V) X.

%add_declaration Th (axiom_decl S X) :- 
%		osyn2rewrite X C L R, 
%		add_axiom Th (user_rewrite S) equiv C L R.



type  all_pred  (X -> o) -> (list X) -> o.

all_pred P nil.
all_pred P (H::T) :- P H, all_pred P T.

% This is also in preparser.mod!

type foldr_pred (A -> B -> B -> o) -> B -> list A -> B -> o.

foldr_pred P X nil X.
foldr_pred P X (W :: L) Z :- foldr_pred P X L Y, P W Y Z.


type allsols  (A -> o) -> list A -> o.
local alls    (A -> o) -> list A -> list A -> o.

allsols Prop L :- alls Prop L nil.

alls Prop L T :- Prop H, not (member H T), alls Prop L (H::T), !.
%alls Prop L T :- Prop H, member H T, alls Prop L T, !.
alls Prop L L.

type sublist (list X) -> (list X) -> o.

sublist Xs Ys :- all_pred (X\ (member X Ys)) Xs.
