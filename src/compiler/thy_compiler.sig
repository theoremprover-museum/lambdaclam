/* 

File: thy_compiler.sig
Description: On-the-fly theory inclusion

*/

sig thy_compiler.

accum_sig envparser.

type use_thy string -> (list o) -> o.

type mytest syn_decl -> o.

type well_formed_decls (list syn_decl) -> o.
type well_formed_decl syn_decl -> o.
type well_formed_type osyn -> o.
type well_formed_sequent osyn -> o.
type well_formed_assertions (list osyn) -> o.
type well_formed_assertion osyn -> o.
type well_typed_term osyn -> osyn -> o.

type new_type string -> o.
type new_const string -> osyn -> o.
type new_axiom string -> o.
type new_inference string -> o.
type new_conjecture string -> o.
type new_predicate string -> (list osyn) -> o.
type new_definition string -> osyn -> osyn -> o.

type sublist (list X) -> (list X) -> o.

kind myprod type.
type mypair int -> (list o) -> myprod.

kind polyprod type -> type -> type.
type polypair A -> B -> (polyprod A B).

kind rewrite_syn type.
type rewrite_osyns osyn -> osyn -> osyn -> rewrite_syn.

% for testing

type import_one_decl  string -> string -> syn_decl -> (list o) -> o.
type import_lclam_decls  string -> string -> (list syn_decl) -> (list o) -> o.
type osyn2rewrite2  (list osyn) -> osyn -> osyn -> osyn -> osyn -> o.
type split_hyps  (list osyn) -> (list osyn) -> (list osyn) -> o.
type allsols  (A -> o) -> list A -> o.
type generic  (list osyn) -> osyn -> o.
type axiom2method  (list osyn) -> osyn -> (list osyn) -> osyn -> o.
type foldr_pred (A -> B -> B -> o) -> B -> list A -> B -> o.


type print_CLR2 string -> string -> rewrite_syn -> myprod -> myprod -> o.
type newvars int -> (list X) -> o.
type ly_nth int -> A -> (list A) -> o.

end