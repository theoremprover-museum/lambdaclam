sig envgrammar.
accum_sig lambdayacc.

%accum_sig logic_eq_constants.
%accum_sig arithmetic.
type nat osyn.

/*

kind osyn type.

type  user_object string -> osyn.

type  app  osyn -> osyn -> osyn.
type  bool osyn.
type  arrow osyn -> osyn -> osyn.
infixr arrow 100.
type  tuple_type (list osyn) -> osyn.
type  otype_of osyn -> osyn -> osyn.
type  trueP  osyn.
type  falseP  osyn.
type  and  osyn.
type  tuple  (list osyn) -> osyn.
type  or  osyn.
type  imp  osyn.
type  eq  osyn.
type  forall  osyn.
type  abs  (osyn -> osyn) -> osyn.

*/


type occur string -> osyn -> osyn.


%%% terminals (gs = grammar symbol)

type productt, arrowt, natt, boolt, lambdat, colont, periodt, commat, overt gs.
type nullaryt, unaryt gs.
type uset, logict, conjt gs.
type predicatet gs.
type semicolont gs.
type definet gs.

type typet gs.
type constt gs.
type axiomt gs.
type theoryt, conjt gs.

type truet, falset, andt, ort, impt, eqt, forallt, existst gs.
type entailst, inferencet gs.
type definet gs.

type lpredparen, rpredparen gs.
type langle, rangle gs.

%type accumulatet gs.

%%% nonterminals

type st, term osyn -> gs.
type two_terms osyn -> osyn -> gs.
type const_decl_gs string -> int -> gs.

kind syn_decl type.
type mk_decl string -> int -> syn_decl.
type term_in_env (list syn_decl) -> osyn -> gs.

type theory_decl_gs string -> string -> (list syn_decl) -> gs.

type syn_decls (list syn_decl) -> gs.
type syn_decl_gs syn_decl -> gs.
type const_decl string -> int -> syn_decl.
type type_decl string -> syn_decl.
type type_decl_gs string -> gs.

type typed_const_decl_gs string -> osyn -> gs.
type typed_const_decl string -> osyn -> syn_decl.

type pred_decl_gs string -> (list osyn) -> gs.
type pred_decl string -> (list osyn) -> syn_decl.

type define_gs string -> osyn -> osyn -> gs.

%type accumulate_decl string -> gs.

%%% abstract syntax constructors

type define string -> osyn -> osyn -> syn_decl.


type logicparser o.

type lparen_type gs.
type lparen_term gs.
type lparen_pred gs.
type lparen_prop gs.

type lparen, rparen, lsqparen, rsqparen gs.
type my_id string -> osyn.
type id_with_type string -> osyn -> osyn.
type typed_abs string -> osyn -> osyn -> osyn.

% (ty_abs type abstraction)
type ty_abs osyn -> (osyn -> osyn) -> osyn.

type my_app osyn -> osyn -> osyn.
type intsyn int -> osyn.


%%% disambiguating nonterminals

% to get round precedence problem, have to distinguish quantified propositions
type qprop_gs osyn -> gs.
type prop_gs osyn -> gs.


type id_eq string -> gs.

type assumptions_gs (list osyn) -> gs.
type assumption_gs osyn -> gs.

type axiom_decl_gs string -> (list osyn) -> osyn -> gs.
type axiom_decl string -> (list osyn) -> osyn -> syn_decl.

type conj_decl_gs string -> (list osyn) -> osyn -> gs.
type conj_decl string -> (list osyn) -> osyn -> syn_decl.

% No side-conditions yet

type inference_decl_gs string -> (list (pairty (list osyn) osyn)) -> (list osyn) -> osyn -> gs.
type inference_decl string -> (list (pairty (list osyn) osyn)) -> (list osyn) -> osyn -> syn_decl.

type sequent_gs (list osyn) -> osyn -> gs.
type sequents_gs (list (pairty (list osyn) osyn)) -> gs.


type formlam  string -> osyn -> (osyn -> osyn) -> o.
type copy osyn -> osyn -> o.

type ly_id2 string -> gs.
type ly_id3 string -> gs.

type const_id_gs string -> gs.
type pred_id_gs string -> gs.

type type_list_gs (list osyn) -> gs.
type type_comma_gs gs.

type pred_paren string -> gs.

type axiom_name string -> gs.

type termeqt osyn -> gs.
