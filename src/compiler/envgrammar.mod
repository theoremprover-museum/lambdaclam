module envgrammar.
accumulate lambdayacc.

type my_id string -> osyn.
type id_with_type string -> osyn -> osyn.
type typed_abs string -> osyn -> osyn -> osyn.
type ty_abs osyn -> (osyn -> osyn) -> osyn.


type my_app osyn -> osyn -> osyn.
type intsyn int -> osyn.


printname _ "(" lparen.
printname _ ")" rparen.
printname _ "[" lsqparen.
printname _ "]" rsqparen.
printname _ "#" productt.
printname _ "->" arrowt.
printname _ "\\" lambdat.
printname _ "/" overt.
printname _ ":" colont.
printname _ "." periodt.
printname _ "," commat.
printname _ ";" semicolont.
printname _ "nat" natt.
printname _ "bool" boolt.
printname _ "nullary" nullaryt.
printname _ "unary" unaryt.
printname _ "type" typet.
printname _ "const" constt.
printname _ "axiom" axiomt.
printname _ "true" truet.
printname _ "false" falset.
printname _ "/\\" andt.
printname _ "\\/" ort.
printname _ "=>" impt.
printname _ "=" eqt.
printname _ "forall" forallt.
printname _ "exists" existst.
printname _ "Theory" theoryt.
printname _ "|-" entailst.
printname _ "inference" inferencet.
printname _ "Use" uset.
printname _ "Logic" logict.
printname _ "conjecture" conjt.
printname _ "predicate" predicatet.
printname _ "define" definet.
printname _ "{" lpredparen.
printname _ "}" rpredparen.
printname _ "<" langle.
printname _ ">" rangle.
%printname _ "Accumulate" accumulatet.

terminal X :-
	oncememb X [lparen, rparen, lsqparen, rsqparen, productt, arrowt, natt, boolt, lambdat, colont, periodt, commat, unaryt, nullaryt, typet, constt, axiomt, truet, falset, andt, ort, impt, eqt, forallt, theoryt, entailst, inferencet, overt, uset, logict, conjt, existst, predicatet, semicolont, definet, lpredparen, rpredparen, langle, rangle].

% ly_id2 was to try to avoid a reduce-reduce conflict between using ids for
% types and terms. Use as a nonterminal. Doesn't work.

terminal X :-
	oncememb X [ly_id A, iconst N, sconst S].


%terminal X :- oncememb X [accumulatet].

%non_terminal X :- member X [ly_id2 A2, ly_id3 A3].

non_terminal X :- member X [term Z, st Y, const_decl_gs S N, term_in_env Ds T, syn_decls Ds, syn_decl_gs D, type_decl_gs S2, assumptions_gs As, assumption_gs A].

non_terminal X :- member X [typed_const_decl_gs S3 T2, axiom_decl_gs S4 Hs Ax, prop_gs P, qprop_gs Q, theory_decl_gs S5 S7 Ds2, inference_decl_gs S6 Seqs H2 C3, sequent_gs H3 C2, sequents_gs Seqs, conj_decl_gs S7 Hs2 Ax2, lparen_type, lparen_term, lparen_pred, lparen_prop, two_terms T1 T6, const_id_gs S8, pred_decl_gs S9 Ts, pred_id_gs S10, type_list_gs Ts2, type_comma_gs, pred_paren P2, axiom_name S11, define_gs S12 T3 T4, id_eq S13, termeqt T5].

ntnum 34.  % 1+number of non_terminals for grammar being considered.


%start_symbol (term T).
start_symbol (theory_decl_gs S L Ds).

type is_const string -> int -> o.

kind syn_decl type.
type mk_decl string -> int -> syn_decl.
type term_in_env (list syn_decl) -> osyn -> gs.
type const_decl string -> int -> syn_decl.
type type_decl string -> syn_decl.
type type_decl_gs string -> gs.
type syn_decls (list syn_decl) -> gs.
type syn_decl_gs syn_decl -> gs.

type typed_const_decl_gs string -> osyn -> gs.
type typed_const_decl string -> osyn -> syn_decl.

type axiom_decl_gs string -> (list osyn) -> osyn -> gs.
type prop_gs osyn -> gs.
type qprop_gs osyn -> gs.
type assumptions_gs (list osyn) -> gs.
type assumption_gs osyn -> gs.

type axiom_decl string -> (list osyn) -> osyn -> syn_decl.

type sequent_gs (list osyn) -> osyn -> gs.

cfg %%% just parsing, no evaluation
[ 
  rule ((theory_decl_gs Th Lo Ds7) ==> [theoryt, ly_id I10, periodt, uset, logict, ly_id I13, periodt, syn_decls Ds8]) (Th = I10, Lo = I13, Ds7 = Ds8),
  rule ((syn_decls Ds4) ==> [syn_decl_gs D]) (Ds4 = [D]),
  rule ((syn_decls Ds5) ==> [syn_decl_gs D2, syn_decls Ds6]) (Ds5 = D2::Ds6),
%  rule ((syn_decl_gs D2) ==> [const_decl_gs S4 N4]) (D2 = const_decl S4 N4),
  rule ((syn_decl_gs D3) ==> [type_decl_gs I5]) (D3 = type_decl I5),
  rule ((syn_decl_gs D4) ==> [typed_const_decl_gs S6 Z6]) (D4 = typed_const_decl S6 Z6),
  rule ((syn_decl_gs D5) ==> [axiom_decl_gs S7 H1 Z7]) (D5 = axiom_decl S7 H1 Z7),
  rule ((syn_decl_gs D6) ==> [inference_decl_gs S12 Seqs4 H6 C6]) (D6 = inference_decl S12 Seqs4 H6 C6),
  rule ((syn_decl_gs D7) ==> [conj_decl_gs S14 Conj_hyps Conj_conc]) (D7 = conj_decl S14 Conj_hyps Conj_conc),
  rule ((syn_decl_gs D8) ==> [pred_decl_gs S15 Types]) (D8 = pred_decl S15 Types),
  rule ((syn_decl_gs D9) ==> [define_gs S20 Z24 Z25]) (D9 = define S20 Z24 Z25),
  rule ((pred_decl_gs S16 Types2) ==> [pred_id_gs S17, type_list_gs Types4, periodt]) (S16 = S17, Types2 = Types4),
rule ((pred_id_gs S16b) ==> [predicatet, ly_id S16c, colont]) (S16b = S16c),
% include colon to avoid ambiguity with forall's
  rule ((type_list_gs Types3) ==> [st X14]) (Types3 = [X14]),
  rule ((type_list_gs Types5) ==> [st X15, type_comma_gs, type_list_gs Types6]) (Types5 = X15::Types6),
  rule (type_comma_gs ==> [commat]) (true),% avoids RR between type and ass list
  rule ((type_decl_gs I3) ==> [typet, ly_id I4, periodt]) (I3 = I4),
%  rule ((term_in_env Ds T) ==> [term T2]) (Ds = [], T = T2),
%  rule ((term_in_env Ds2 T3) ==> [const_decl_gs S3 N3, term_in_env Ds3 T4]) (Ds2 = (mk_decl S3 N3)::Ds3, T3 = T4), 
  rule ((term X0) ==> [lparen_term, ly_id I, colont, st T, lambdat, term X, rparen]) (formlam I X L, X0 = (ty_abs T L)),
  rule ((term X0) ==> [lparen, ly_id I, colont, st T, lambdat, term X, rparen]) (formlam I X L, X0 = (ty_abs T L)),  
  rule ((term X7) ==> [ly_id I]) (X7 = (user_object I)), % instead of my_id I
%  rule ((two_terms T1 T2) ==> [term T1b, term T2b]) (T1 = T1b, T2 = T2b),
%  rule ((term X8) ==> [lparen_term, term X9, term X10, rparen]) (X8 = (app X9 X10)),
%  rule ((term X8) ==> [lparen, term X9, term X10, rparen]) (X8 = (app X9 X10)),
  rule ((term X8) ==> [langle, term X9, term X10, rangle]) (X8 = (app X9 X10)),
  rule ((st X1) ==> [natt]) (X1 = nat),
  rule ((st X2) ==> [boolt]) (X2 = bool),
  rule ((st X3) ==> [lparen_type, (st X6), rparen]) (X3 = X6),
  rule (lparen_type ==> [lparen]) true,
%  rule (lparen_term ==> [lparen]) true,
  rule (lparen_prop ==> [lparen]) true,
  rule ((st Z1) ==> [(st X4),arrowt,(st Y1)]) (Z1 = (X4 arrow Y1)),
  rule ((st Z2) ==> [(st X5),productt,(st Y2)]) (Z2 = (tuple_type [X5,Y2])),
  rule ((st Z16) ==> [ly_id Z17]) (Z16 = user_object Z17),
%  rule ((ly_id2 Z18) ==> [ly_id Z19]) (Z18 = Z19),
%  rule ((ly_id3 Z18b) ==> [ly_id Z19b]) (Z18b = Z19b),
 rule ((const_decl_gs S2 N2) ==> [nullaryt, ly_id I4, periodt]) (S2 = I4, N2 = 0),
 rule ((const_decl_gs S1 N1) ==> [unaryt, ly_id I2, periodt]) (S1 = I2, N1 = 1),
 rule ((axiom_decl_gs S5 H2 Z5) ==> [axiomt, axiom_name I6, qprop_gs Z3, periodt]) (S5 = I6, Z5 = Z3, H2 = []),
 rule ((axiom_name I14) ==> [ly_id I15]) (I14 = I15),
 rule ((axiom_decl_gs S10 H3 Z11) ==> [axiomt, ly_id I11, lsqparen, sequent_gs Z12 Z13, rsqparen,  periodt]) (S10 = I11, Z11 = Z13, H3 = Z12),
 rule ((conj_decl_gs S10b H3b Z11b) ==> [conjt, ly_id I11b, lsqparen, sequent_gs Z12b Z13b, rsqparen,  periodt]) (S10b = I11b, Z11b = Z13b, H3b = Z12b),
 rule ((define_gs S18 Z20 Z21) ==> [definet, constt, ly_id S19, colont, st Z22, eqt, term Z23, periodt]) (S18 = S19, Z20 = Z23, Z21 = Z22),
 rule ((id_eq S23) ==> [ly_id S24, eqt])  (S23 = S24),
 rule ((define_gs S21 Z26 Z27) ==> [definet, typet, id_eq S22, st Z28, periodt]) (S21 = S22, Z26 = Z28, Z27 = universe),
% rule ((define_gs S21 Z26 Z27) ==> [definet, typet, ly_id S22, eqt, st Z28, periodt]) (S21 = S22, Z26 = Z28, Z27 = universe),
 rule ((assumptions_gs As3) ==> [assumption_gs A5, commat, assumptions_gs As4]) (As3 = A5::As4),
 rule ((assumptions_gs As5) ==> [assumption_gs Ass3]) (As5 = [Ass3]),
 rule ((assumption_gs Ass) ==> [qprop_gs P16]) (Ass = P16),
 rule ((assumption_gs Ass2) ==> [ly_id I12, colont, st T5]) (Ass2 = otype_of (user_object I12) T5),
 rule ((inference_decl_gs S11 Seqs3 H7 C7) ==> [inferencet, ly_id S13, lsqparen, sequents_gs Seqs2, overt, sequent_gs H10 P18, rsqparen, periodt]) (S11 = S13, Seqs3 = Seqs2, H7 = H10, C7 = P18),
 rule ((sequents_gs Seqs) ==> [sequent_gs H11 C11]) (Seqs = [pair H11 C11]),
 rule ((sequents_gs Seqs5) ==> [sequent_gs H12 C12, semicolont, sequents_gs Seqs7]) (Seqs5 = (pair H12 C12)::Seqs7),
 rule ((sequent_gs H8 C8) ==> [assumptions_gs Z14, entailst, qprop_gs Z15]) (H8 = Z14, C8 = Z15),%should allow empty assumption list
 rule ((typed_const_decl_gs S9 Z9) ==> [const_id_gs I9, st Z10, periodt]) (S9 = I9, Z9 = Z10),
 rule ((const_id_gs I9b) ==> [constt, ly_id I9c]) (I9b = I9c),
 rule ((prop_gs P0) ==> [lparen, qprop_gs Pn, rparen]) (P0 = Pn),
% rule ((prop_gs P0) ==> [lparen_prop, qprop_gs Pn, rparen]) (P0 = Pn),
 rule ((prop_gs P2) ==> [truet]) (P2 = trueP),
 rule ((prop_gs P3) ==> [falset]) (P3 = falseP),
% rule (lparen_pred ==> [lparen]) true,
rule (lparen_pred ==> [lpredparen]) true,
 rule ((pred_paren Pred2) ==> [ly_id Pred3, lparen_pred]) (Pred2 = Pred3),
 rule ((prop_gs P17) ==> [pred_paren Pred, term X13, rpredparen]) (P17 = (app (user_object Pred) X13)),
% rule ((prop_gs P17) ==> [ly_id Pred, lparen_pred, term X13, rparen]) (P17 = (app (user_object Pred) X13)),
% rule ((prop_gs P17) ==> [ly_id Pred, lparen, term X13, rparen]) (P17 = (app (user_object Pred) X13)),
% This could be dodgy
 rule ((prop_gs P23) ==> [ly_id S25]) (P23 = (user_object S25)),
 rule ((prop_gs P4) ==> [prop_gs P5, andt, prop_gs P6]) (P4 = (app and (tuple [P5, P6]))),
 rule ((prop_gs P7) ==> [prop_gs P8, ort, prop_gs P9]) (P7 = (app or (tuple [P8, P9]))),
 rule ((prop_gs P10) ==> [prop_gs P11, impt, prop_gs P12]) (P10 = (app imp (tuple [P11, P12]))),
% rule ((prop_gs P13) ==> [term X11, eqt, term X12]) (P13 = (app eq (tuple [X11, X12]))),
 rule ((prop_gs P13) ==> [langle, termeqt X11, term X12, rangle]) (P13 = (app eq (tuple [X11, X12]))),
% rule ((prop_gs P24) ==> [prop_gs P25, lsqparen, ly_id Var, rsqparen]) (P24 = occur Var P25),
 rule ((termeqt T6) ==> [term T7, eqt]) (T6 = T7),
 rule ((qprop_gs P14) ==> [forallt, ly_id I7, colont, st Y3, periodt, prop_gs P15]) (formlam I7 P15 L2, P14 = (app forall (tuple [Y3, (abs L2)]))),
 rule ((qprop_gs P21) ==> [existst, ly_id I8, colont, st Y4, periodt, prop_gs P22]) (formlam I8 P22 L3, P21 = (app exists (tuple [Y4, abs L3]))),
 rule ((qprop_gs P19) ==> [prop_gs P20]) (P19 = P20)
].

% precedence and associativity.  needed to resolve shift-reduce conflicts:
% x binds tighter than ->

binaryop arrowt (st X) (st Y) "right" 2.
binaryop productt (st X) (st Y) "left" 1.


% /\ tighter than \/ tighter than =>

binaryop andt (prop_gs P) (prop_gs Q) "left" 1.
binaryop ort (prop_gs P) (prop_gs Q) "left" 2.
binaryop impt (prop_gs P) (prop_gs Q) "right" 3.

%binaryop forallt (st T) (prop_gs P) "left" 4. 


% freshcopy clauses:  (needed because of an implementation characteristic)

freshcopy (term_in_env D1 T1) (term_in_env D2 T2) :- !.
freshcopy (term X) (term Y) :- !.
freshcopy (two_terms X1 Y1) (two_terms X2 Y2) :- !.
freshcopy (const_decl_gs S1 N1) (const_decl_gs S2 N2) :- !.
freshcopy (axiom_decl_gs S3 H1 A3) (axiom_decl_gs S4 H2 A4) :- !.
freshcopy (conj_decl_gs S3 H1 A3) (conj_decl_gs S4 H2 A4) :- !.
freshcopy (typed_const_decl_gs S1 T1) (typed_const_decl_gs S2 T2) :- !.
freshcopy (type_decl_gs I1) (type_decl_gs I2) :- !.
freshcopy (st X) (st Y) :- !.
freshcopy (syn_decls Ds1) (syn_decls Ds2) :- !.
freshcopy (syn_decl_gs D1) (syn_decl_gs D2) :- !.
freshcopy (prop_gs P) (prop_gs P2) :- !.
freshcopy (qprop_gs Q) (qprop_gs Q2) :- !.
freshcopy (assumptions_gs As) (assumptions_gs As2) :- !.
freshcopy (assumption_gs A) (assumption_gs A2) :- !.
freshcopy (theory_decl_gs S1 L1 Th1) (theory_decl_gs S2 L2 Th2) :- !.
freshcopy (inference_decl_gs S1 Hyps H2 C2) (inference_decl_gs S2 Hyps2 H4 C4) :-!.
freshcopy (sequent_gs H4 C4) (sequent_gs H5 C5) :-!.
freshcopy (sequents_gs Seqs) (sequents_gs Seqs2) :-!.
%freshcopy (ly_id2 A) (ly_id2 A2) :- !.
%freshcopy (ly_id3 A) (ly_id3 A2) :- !.
freshcopy (const_id_gs S) (const_id_gs S2) :- !.
freshcopy (pred_decl_gs S Ts) (pred_decl_gs S2 Ts2) :- !.
freshcopy (pred_id_gs S) (pred_id_gs S2) :- !.
freshcopy (type_list_gs Ts) (type_list_gs Ts2) :- !.
freshcopy (pred_paren P) (pred_paren P2) :- !.
freshcopy (axiom_name S) (axiom_name S2) :- !.
freshcopy (define_gs S Ta Tb) (define_gs S2 Ta2 Tb2) :- !.
freshcopy (id_eq S) (id_eq S2) :- !.
freshcopy (termeqt T1) (termeqt T2) :-!.
freshcopy T T.

% semantic action clauses

% Also need clauses for type constructors.

copy (app A B) (app C D) :- !,copy A C, copy B D.
copy (abs L) (abs M) :- !,pi x\ (copy x x => (copy (L x) (M x))).
copy (tuple []) (tuple []) :- !.
copy (tuple (T::Ts)) (tuple (U::Us)) :- !, copy T U, copy (tuple Ts) (tuple Us).
copy (ty_abs T L) (ty_abs U M) :- !, copy T U, copy (abs L) (abs M).
copy X X.
%copy (my_id S) (my_id S).   % will be superceded by !


formlam S B L :-
  pi x\ ((copy (user_object S) x :- !) => copy B (L x)).


% test the parsers

logicparser :-
	parseline (theory_decl_gs Th Lo Ds),
	printterm std_out Th, print "\n",
	printterm std_out Lo, print "\n",
	printterm std_out Ds, print "\n",
	logicparser.
