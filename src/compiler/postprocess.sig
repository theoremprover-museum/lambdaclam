sig postprocess.
accum_sig envparser. 

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

type decl2binding syn_decl -> o -> o.
type decl2lclam  out_stream -> out_stream -> string -> string -> syn_decl -> o.


%type droll int -> o.
type droll (list string) -> o.

type add_declarations theory -> (list syn_decl) -> o.
type add_declaration theory -> syn_decl -> o.

type osyn2rewrite  osyn -> osyn -> osyn -> osyn -> o.
type osyn2rewrite2 (list osyn) -> osyn -> osyn -> osyn -> osyn -> o.

type process_file string -> o.
type generate-clam string -> string -> (list syn_decl) -> o.

type balerno (list o) -> o -> o.
type curry (list o) -> o -> o.

type curry2 (list o) -> o -> o -> o.

type make_bindings theory -> (list syn_decl) -> (list o) -> o.

type make_binding theory -> syn_decl -> o -> o.

type lower string -> string -> o.
type allsols  (A -> o) -> list A -> o.

type split_hyps  (list osyn) -> (list osyn) -> (list osyn) -> o.
type combine  (list osyn) -> osyn -> osyn -> osyn -> (list osyn) -> osyn -> 
osyn -> o.
type strip_true  (list osyn) -> (list osyn) -> o.
type conjoin  (list osyn) -> osyn -> o.
type abstract  (list osyn) -> osyn -> osyn -> o.
type newvar osyn -> o.

type newvars int -> (list X) -> o.
type apply (list X) -> osyn -> osyn -> o.
type abstract2  (list osyn) -> osyn -> osyn -> o.

type generic  (list osyn) -> osyn -> o.
type axiom2method  (list osyn) -> osyn -> (list osyn) -> osyn -> o.

type getAnts  (pairty (list osyn) osyn) -> (list osyn) -> o.
type getSucc  (pairty (list osyn) osyn) -> osyn -> o.

type not_context_var osyn -> o.

type abstract3 osyn -> int -> osyn -> o.

type getVars osyn -> (list osyn) -> o.
type subterm osyn -> osyn -> o.

type tuplify (list osyn) -> osyn -> o.
type untuplify osyn -> (list osyn) -> o.

type  replace_hyps2  out_stream -> list osyn -> list osyn -> int -> int -> o.

type foldr_pred (A -> B -> B -> o) -> B -> list A -> B -> o.
