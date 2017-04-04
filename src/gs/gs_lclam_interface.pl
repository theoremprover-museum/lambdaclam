
/* ************************************************* */ 
/* Module for comunication between the GS framework
   in LambdaProlog and decision procedures implemented in PROLOG
   See also the file gs_framework.mod

   Author: Predrag Janicic
*/   

:- use_module(library(charsio)).
:- use_module(library(tcp)).

:- op(850,xfy,[:]). 
:- op(850,xfy,=>).
:- op(850,xfy,#).
:- op(700,yfx,in).
:- op(700,yfx,=).
:- op(850,xfy,\).
:- op(850,xfy,<=>).


/* ************************************************* */
/*
   Predicates used by the underlying decision procedures;
   These predicates were available in the old Clam, but
   now given them implemented here, the underlying decision
   procedures are stand alone
*/
   

member(A,[A|_]).
member(A,[B|L]):- not(var(A)), not(A=B), !, member(A,L).
member(A,[_|L]):- member(A,L).

not(A):- \+ A.

canonical_form(F,[],F) :- !.
canonical_form(F, LE, FF) :-
    member((_:L=R in _), LE),
    replace_all(L,R,F,F1),
    not(F=F1),!,
    canonical_form(F1, LE, FF).
canonical_form(F,_,F).
% LE is a list of canonical set of rewrite rules

union(L1,L2,LL) :-
	append(L1,L2,L3),
	remove_multiples(L3,LL).

remove_multiples(L,LL):-
	member(A,L),
	num_of_occs(A,L,N),
	N>1,!,
	delete(L,A,L1),
	append([A], L1, L2),
	remove_multiples(L2,LL).
remove_multiples(L,L).
	

delete([],_,[]):- !.
delete([X|L],X,LL):- !,delete(L,X,LL).
delete([Y|L],X,[Y|LL]) :- delete(L,X,LL).

num_of_occs(_, [], 0) :- !.
num_of_occs(X, [X|L], N) :- !, num_of_occs(X, L, N1), N is N1+1.
num_of_occs(X, [_|L], N) :- num_of_occs(X,L,N).

% there is a predicate exp_at in Clam 2.7
% here we use a stand-alone substitute
exp_at(A,_,A).
exp_at(A,_,B) :- (A) =..[F, C], (exp_at(C,_,B) ;  exp_at(F,_,B)).
exp_at(A,_,B) :- (A) =..[F, C, D], (exp_at(C,_,B) ; ((exp_at(D,_,B) ; exp_at(F,_,B)))).
exp_at(_,_,_) :- fail.


replace_all(L,R,L,R):-!. 
replace_all(L,R,F,FF):- (F) =.. [G, A],!, replace_all(L,R,G,GG), replace_all(L,R,A,AA), FF =.. [GG,AA].
replace_all(L,R,F,FF):- (F) =.. [G, A, B],!, replace_all(L,R,G,GG), replace_all(L,R,A,AA), replace_all(L,R,B,BB), (FF) =.. [GG,AA,BB].
replace_all(_,_,F,F).


/* ************************************************* */
/* Support for converting formulae from abstract
   LambdaClam syntax to concrete the old Clam's syntax
*/

gs_convert_list_to_lclam_syntax([],[]).
gs_convert_list_to_lclam_syntax([A|L],[AS|LS]):-
	gs_convert_to_lclam_syntax(A,AS),
	gs_convert_list_to_lclam_syntax(L,LS).



gs_get_oyster_term_from_string(String,Term):-
	replace_bad_chars1(String,String1),
	name(String1,L),
	chars_to_stream(L,Stream),
	read(Stream,Term).

gs_convert_to_lclam_syntax(X, XString) :-
	gs_convert_to_lclam_syntax_(X,XS),
	replace_bad_chars2(XS,XString).

gs_convert_to_lclam_syntax_( void, 'falseP') :- !.
gs_convert_to_lclam_syntax_( {true}, 'trueP') :- !.
gs_convert_to_lclam_syntax_( 0, 'zero') :- !.
gs_convert_to_lclam_syntax_( (X=>void), XString) :-
	!,
	gs_convert_to_lclam_syntax_(X,XS),
	name('(app neg ',L1),
	name(XS,L2),
	append(L1,L2,L3),
	name(')',L4),
	append(L3,L4,L),
	name(XString,L).

gs_convert_to_lclam_syntax_( A=B in _, XString) :-
	!,
	gs_convert_to_lclam_syntax_(A,AS),
	gs_convert_to_lclam_syntax_(B,BS),
	name('(app ',L1),
        name(eq,L2),
	append(L1,L2,L3),
	name(' (tuple[',L4),
	append(L3,L4,L5),
	name(AS,L6),
	append(L5,L6,L7),
	name(', ',L8),
	append(L7,L8,L9),
	name(BS,L10),
	append(L9,L10,L11),
	name(']))',L12),
	append(L11,L12,L13),
	name(XString,L13).


gs_convert_to_lclam_syntax_( (A#B), XString) :-
	!,
	gs_convert_to_lclam_syntax_(A,AS),
	gs_convert_to_lclam_syntax_(B,BS),
	name('(app ',L1),
        name('and',L2),
	append(L1,L2,L3),
	name(' (tuple[ ',L4),
	append(L3,L4,L5),
	name(AS,L6),
	append(L5,L6,L7),
	name(', ',L8),
	append(L7,L8,L9),
	name(BS,L10),
	append(L9,L10,L11),
	name(']))',L12),
	append(L11,L12,L13),
	name(XString,L13).


gs_convert_to_lclam_syntax_( (A\B), XString) :-
	!,
	gs_convert_to_lclam_syntax_(A,AS),
	gs_convert_to_lclam_syntax_(B,BS),
	name('(app ',L1),
        name('or',L2),
	append(L1,L2,L3),
	name(' (tuple[',L4),
	append(L3,L4,L5),
	name(AS,L6),
	append(L5,L6,L7),
	name(', ',L8),
	append(L7,L8,L9),
	name(BS,L10),
	append(L9,L10,L11),
	name(']))',L12),
	append(L11,L12,L13),
	name(XString,L13).


gs_convert_to_lclam_syntax_(X, XString) :-
	not(atom(X)),
	X =.. [O,A],
	!,
	gs_convert_to_lclam_syntax_(A,AS),
	name('(app ',L1),
        name(O,L2),
	append(L1,L2,L3),
	name(' ',L4),
	append(L3,L4,L6),
	name(AS,L7),
	append(L6,L7,L8),
	name(')',L12),
	append(L8,L12,L13),
	name(XString,L13).

gs_convert_to_lclam_syntax_( X, XString) :-
	not(atom(X)),
	X =.. [O,A,B],
	!,
	gs_convert_to_lclam_syntax_(A,AS),
	gs_convert_to_lclam_syntax_(B,BS),
	name('(app ',L1),
        name(O,L2),
	append(L1,L2,L3),
	name(' (tuple[',L4),
	append(L3,L4,L5),
	name(AS,L6),
	append(L5,L6,L7),
	name(', ',L8),
	append(L7,L8,L9),
	name(BS,L10),
	append(L9,L10,L11),
	name(']))',L12),
	append(L11,L12,L13),
	name(XString,L13).

gs_convert_to_lclam_syntax_(X,X).

replace_bad_chars1(S1,S2):-
	name(S1,N1),
	replace_bad_chars_in_list1(N1,N2),
	name(S2,N2).

replace_bad_chars_in_list1([],[]).

replace_bad_chars_in_list1([61,62|L],[61,62|LL]):- !, % dont replace =>
	replace_bad_chars_in_list1(L,LL).


replace_bad_chars_in_list1([60|L],[118,95,48,49|LL]):- !, % replace <
	replace_bad_chars_in_list1(L,LL).
replace_bad_chars_in_list1([62|L],[118,95,48,50|LL]):- !, % replace >
	replace_bad_chars_in_list1(L,LL).
replace_bad_chars_in_list1([45|L],[118,95,48,51|LL]):- !, % replace -
	replace_bad_chars_in_list1(L,LL).
replace_bad_chars_in_list1([C|L],[C|LL]):- 
	replace_bad_chars_in_list1(L,LL).


replace_bad_chars2(S1,S2):-
	name(S1,N1),
	replace_bad_chars_in_list2(N1,N2),
	name(S2,N2).

replace_bad_chars_in_list2([],[]).
replace_bad_chars_in_list2([118,95,48,49|L],[60|LL]):- !,
	replace_bad_chars_in_list2(L,LL).
replace_bad_chars_in_list2([118,95,48,50|L],[62|LL]):- !,
	replace_bad_chars_in_list2(L,LL).
replace_bad_chars_in_list2([118,95,48,51|L],[45|LL]):- !,
	replace_bad_chars_in_list2(L,LL).
replace_bad_chars_in_list2([C|L],[C|LL]):-
	replace_bad_chars_in_list2(L,LL).


/* ************************************************* */
/* Calls to underlying decision procedures
*/


gs_ccc(OysterString,LClamString):-
	gs_get_oyster_term_from_string(OysterString,F),
	transform_conjunction_to_list(F,L),
	ccc(L,L1),
	(L1 = [] -> LL1 = [ {true} ] ; LL1 = L1),
	negate_all_literals(LL1,L2),
	gs_convert_list_to_lclam_syntax(L2,F1),
	make_disjunction(F1,F2),
	replace_bad_chars2(F2,LClamString).


gs_valid(pia,OysterString,'trueP'):-
	gs_get_oyster_term_from_string(OysterString,F),
	eliminate_p(F,F1),
	uni_closure(F1,F2,_,pnat),
	dp_pia(hodes,F2,A),
	A={true}, !.
gs_valid(pia,_,'falseP').


gs_cooper(pia,F,FF):-
	gs_get_oyster_term_from_string(F,F1),
	uni_closure(F1,F2,_,pnat),
	eliminate_p(F2,F3),
	dp_pia_once(cooper,F3,F4),
	simplify_pia_(F4,F5),
	eliminate_numerals(F5,F6),
	strip_quantifiers(F6,F7),
	gs_convert_to_lclam_syntax(F7,F8),
	replace_bad_chars2(F8,FF).

gs_hodes(pia,F,FF):-
	gs_get_oyster_term_from_string(F,F1),
	uni_closure(F1,F2,_,pnat),
	eliminate_p(F2,F3),
	dp_pia_once(hodes,F3,F4),
	simplify_pia_(F4,F5),
	eliminate_numerals(F5,F6),
	strip_quantifiers(F6,F7),
	gs_convert_to_lclam_syntax(F7,F8),
	replace_bad_chars2(F8,FF).

gs_solve(pia,OysterString,LClamString):-
	gs_get_oyster_term_from_string(OysterString,L=>void),
	eliminate_p(L,L_p),
        simplify_pia_(L_p,L1),
        check_afs([L1],[L2]),
        (L2=void
	->  L3={true}
	;   L2= {true}
	->  L3=void
	;   (simplify_pia_(L2,L0),solve_one(L0,Ls),
	    L3=(Ls=>void),
	\+ (L_p=>void) = L3)),
	!,
	eliminate_numerals(L3,L4),
	gs_convert_to_lclam_syntax(L4,LClamString).

gs_solve(pia,OysterString,LClamString):-
	gs_get_oyster_term_from_string(OysterString,L),
	eliminate_p(L,L_p),
	simplify_pia_(L_p,L1),
	check_afs([L1],[Lc]),
	( (Lc=void ; Lc={true}) -> L3=Lc 
	;   (simplify_pia_(L1,L2),solve_one(L2,L3))),
	\+ L3=L1,
	!,
	eliminate_numerals(L3,L4),	
	gs_convert_to_lclam_syntax(L4,LClamString).

gs_solve(pia, L ,LL) :-
	gs_get_oyster_term_from_string(L,L1),
	gs_convert_to_lclam_syntax(L1,LL).

gs_simpl_pia(OysterString,LClamString):-
	gs_get_oyster_term_from_string(OysterString,F),
	eliminate_p(F,F1),
	transform_conjunction_to_list(F1,L),
	simpl_pia(L,L1),
	eliminate_numerals(L1,L2),
	gs_convert_list_to_lclam_syntax(L2,F2),
	make_disjunction(F2,F3),
	replace_bad_chars2(F3,LClamString).


% ***************************************************


solve_one(F,FF):- simplify_pia_(F,F1),solve_one_(F1,FF).

solve_one_(times(N,V)=times(N,U) in pnat,V=U in pnat):-!.
solve_one_(F,F).


simpl_pia(F,FF):-
	check_afs(F,F1),
	simpl_afs(F1,FF).
%	\+ equal_eq_sets(F,FF).


simpl(_,L,L):- \+ L=[].
simpl(_,[],[{true}]).


check_afs([],[]).
check_afs([Af|L],[{true}|L1]):-valid_prop(Af),!,check_afs(L,L1).
check_afs([Af|L],[void|L1]):-invalid_pia_(Af),!,check_afs(L,L1).
check_afs([Af|L],[{true}|L1]):-valid_pia_(Af),!,check_afs(L,L1).
check_afs([Af|L],[void|L1]):-invalid_prop(Af),!,check_afs(L,L1).
check_afs([Af|L],[Af|L1]):- check_afs(L,L1).

valid_pia_(A):- %is_T_atomic_formula(pia,A),
                list_of_vars(A,[]),
		dp_pia(hodes,A,{true}).
invalid_pia_(A):-
		%is_T_atomic_formula(pia,A),
                list_of_vars(A,[]),
		dp_pia(hodes,A,{false}).


simpl_afs([{true}|L],[{true}|L1]):-!,
              simpl_afs(L,L1).
simpl_afs([void|L],[void|L1]):-!,
              simpl_afs(L,L1).
simpl_afs([],[]).
simpl_afs([Af=>void|L],[Aff=>void|L1]):-
              %is_T_atomic_formula(pia,Af),
	      !,
              simplify_pia_(Af,Aff),
              simpl_afs(L,L1).
simpl_afs([Af|L],[Aff|L1]):-
              %is_T_atomic_formula(pia,Af),
	      !,
              simplify_pia_(Af,Aff),
              simpl_afs(L,L1).
simpl_afs([Af|L],[Af|L1]):-
              simpl_afs(L,L1).


remove_const(A,AA):- exp_at(A,_,times(N,N1)),
                     number(N),number(N1),!,
                     N2 is N*N1,
                     replace_all(times(N,N1),N2,A,A1),
                     remove_const(A1,AA).
remove_const(A,AA):- exp_at(A,_,times(1,V)),!,
                     replace_all(times(1,V),V,A,A1),
                     remove_const(A1,AA).
remove_const(A,A):-!.


number_of_occs(_,[],0).
number_of_occs(A,[A|L],N):-!,number_of_occs(A,L,N1),N is N1+1.
number_of_occs(A,[_|L],N):-number_of_occs(A,L,N).

valid_prop({true}):-!.
valid_prop(A#B):-!,valid_prop(A),valid_prop(B).
valid_prop(A\B):-!,(valid_prop(A);valid_prop(B)).
valid_prop(A=>B):-!,(invalid_prop(A);valid_prop(B)).

invalid_prop(void):-!.
invalid_prop(A#B):-!,(invalid_prop(A);invalid_prop(B)).
invalid_prop(A\B):-!,(invalid_prop(A),invalid_prop(B)).
invalid_prop(A=>B):-!,(valid_prop(A),invalid_prop(B)).



simplify_pia_(F,FF) :-
   remove_pia(s,F,F2), 
   remove_pia(=>,F2,F3),
   remove_pia(greater,F3,F4),
   remove_pia(less,F4,F5),   
   remove_pia(geq,F5,F6),
   %listof(V,F6^pa_var(F6,V),Lvars),
   list_of_vars(F6,Lvars),
   sort(Lvars,Lvars1),
%   reverse(Lvars1,Lvars2),
   Lvars2 = Lvars1,
   simpl_var(F6,1,F7),
   simpl_vars(F7,Lvars2,F8),
   remove_const(F8,FF).

simpl_vars(F,[],F).
simpl_vars(F,[V|L],FF):-
   simpl_var(F,V,F1),
   simpl_vars(F1,L,FF).

simpl_var(F,V,FF):-
   reorder_pia(V,F,F7),
   collect_pia(V,F7,F8),
   isolate_pia(V,F8,FF).





/* ***************************************************** */
/* Miscellaneous
*/


transform_conjunction_to_list(F1#F2,L):- !,
	transform_conjunction_to_list(F1,L1),
	transform_conjunction_to_list(F2,L2),
	append(L1,L2,L).
transform_conjunction_to_list(F,[F]).


negate_all_literals([],[]).
negate_all_literals([A|L],[B|LL]):-
	negate_literal(A,B),
	negate_all_literals(L,LL).




negate_literal(void,{true}):-!.
negate_literal({true},void):-!.
negate_literal((F=>void),F):-!.
negate_literal(F,(F=>void)).


make_disjunction([A],A) :- !.
make_disjunction([A|L],S):-
	name(A,L1),
	name('(app or (tuple[',L2),
	append(L2,L1,L3),
	name(' , ',L4),
	append(L3,L4,L5),
	make_disjunction(L,S1),
	name(S1,L6),
	append(L5,L6,L7),
	name(' ]))',L8),
	append(L7,L8,L9),
	name(S,L9).

uni_closure(F,F1,A,Sort):-
	list_of_vars(F,A), 
	add_u_quantors(F,A,F1,Sort).

add_u_quantors(F,[],F,_Sort). 
add_u_quantors(F,[V|L1],F1,Sort):-
	add_u_quantors(F,L1,F2,Sort), 
	functor(F1,:,2),
	arg(1,F1,V), 
	arg(2,F1,F3), 
	functor(F3,=>,2), 
	arg(1,F3,Sort), 
	arg(2,F3,F2).

exi_closure(F,F1,A,Sort):-
	list_of_vars(F,A), 
	add_e_quantors(F,A,F1,Sort).


add_e_quantors(F,[],F,_Sort). 
add_e_quantors(F,[V|L1],F1,Sort):-
	add_e_quantors(F,L1,F2,Sort), 
	functor(F1,:,2),
	arg(1,F1,V), 
	arg(2,F1,F3), 
	functor(F3,#,2), 
	arg(1,F3,Sort), 
	arg(2,F3,F2).

list_of_vars([],[]):-!.
list_of_vars([F|L],LV):-!,list_of_vars(F,L1),
                        list_of_vars(L,L2),
                        union(L1,L2,LV).

list_of_vars({true},[]):-!. 
%list_of_vars(list of pnat,[]):-!. 
list_of_vars(pnat,[]):-!.
list_of_vars([],[]):-!.
list_of_vars([X|L],A):-!,list_of_vars(X,A1),
                       list_of_vars(L,A2),
                       union(A1,A2,A).
list_of_vars(F,A):-functor(F,_,Ar),Ar>0,!,
                   F=..[_|L],
                   list_of_vars(L,A).
list_of_vars(F,[]):-integer(F),!. 
list_of_vars(void,[]):-!. 
list_of_vars(generic_type,[]):-!.
list_of_vars(pnat,[]):-!.
list_of_vars(int,[]):-!.
list_of_vars(F,[F]):-atom(F).

strip_quantifiers(_:_=>F,FF):- !,strip_quantifiers(F,FF).
strip_quantifiers(F,F).


eliminate_p(F,FF):-
	exp_at(F,_,pred(N)),!,
	eliminate_p_(pred(N),NN),
	replace_all(pred(N),NN,F,F1),
	eliminate_p(F1,FF).
eliminate_p(F,F).

eliminate_p_(pred(N),N1):- number(N),!,N1 is N-1.
eliminate_p_(pred(N),plus(NN,(times(-1,1)))):- !,eliminate_p_(N,NN).
eliminate_p_(N,N).

eliminate_numerals(F,FF):-
	exp_at(F,_,times(-1,N)),number(N),N>0,!,
	construct_pterm(N,T),
	replace_all(times(-1,N),T,F,F1),
	eliminate_numerals(F1,FF).
eliminate_numerals(F,FF):-
	exp_at(F,_,times(N,T)),number(N),N>1,!,
	N1 is N-1,
	replace_all(times(N,T),plus(T,times(N1,T)),F,F1),
	eliminate_numerals(F1,FF).
eliminate_numerals(F,FF):-
	exp_at(F,_,times(N,T)),number(N),N=1,!,
	replace_all(times(N,T),T,F,F1),
	eliminate_numerals(F1,FF).
eliminate_numerals(F,FF):-
	exp_at(F,_,times(N,T)),number(N),N=0,!,
	replace_all(times(N,T),0,F,F1),
	eliminate_numerals(F1,FF).
eliminate_numerals(F,FF):-
	exp_at(F,_,N),number(N),N>0,!,
	construct_sterm(N,T),
	replace_all(N,T,F,F1),
	eliminate_numerals(F1,FF).
eliminate_numerals(F,FF):-
	exp_at(F,_,times(N,T)),number(N),N<0,!,
	N1 is -N,
	construct_pterm(N1,T1),
	replace_all(times(N,T),times(T1,T),F,F1),
	eliminate_numerals(F1,FF).
eliminate_numerals(F,FF):-
	exp_at(F,_,N),number(N),N<0,!,
	N1 is -N,
	construct_pterm(N1,T),
	replace_all(N,T,F,F1),
	eliminate_numerals(F1,FF).

eliminate_numerals(F,F).



construct_pterm(1,pred(0)):-!.
construct_pterm(N,pred(T)) :- N1 is N-1, construct_pterm(N1,T).

construct_sterm(1,s(0)):-!.
construct_sterm(N,s(T)) :- N1 is N-1, construct_sterm(N1,T).

	

%gs_entail
%gs_simpl


/* ***************************************************** */
/* Communication predicates
*/

waitforrequest :-
	tcp_listen('/tmp/serverfile',_X),
	loop.

loop:-
	repeat,
	tcp_select(X),
	nl,write('>------------ '),write(X),nl,
	dispatch(X),
	loop.

dispatch(connected(X)) :-
	!,
	current_output(CO),
	tcp_output_stream(X, O),
%	nl,write('< '),write('connected'),nl,
	set_output(O),
	write('connected'),put(10),
	flush_output(O),set_output(CO),
	nl,write('--------------------'),
	nl,write('Connected. '),
	write('Socket: '),write(X),nl,ttyflush.

dispatch(term(Socket,gs_ccc(OysterString))) :-
	!,
	write('Rule invoked: ccc'),nl,
	write('PROLOG Input:  '),write(OysterString),nl,
	gs_ccc(OysterString,LClamString),
	write('PROLOG Output: '),write(LClamString),nl,
%	nl,write('< '),write(LClamString),nl,
	current_output(CO),
	tcp_output_stream(Socket, O),
	set_output(O),
	write(LClamString),put(10),
	flush_output(O),set_output(CO),
	write('Disconnected. Waiting for request...'),nl,
	ttyflush,
	tcp_shutdown(Socket).


dispatch(term(Socket,gs_valid_pna(OysterString))) :-
	!,
	write('Rule invoked: gs_valid_pna'),nl,
	write('PROLOG Input:  '),write(OysterString),nl,
	gs_valid(pna,OysterString,LClamString),
	write('PROLOG Output: '),write(LClamString),nl,
%	nl,write('< '),write(LClamString),nl,
	current_output(CO),
	tcp_output_stream(Socket, O),
	set_output(O),
	write(LClamString),put(10),
	flush_output(O),set_output(CO),
	write('Disconnected. Waiting for request...'),nl,
	ttyflush,
	tcp_shutdown(Socket).


dispatch(term(Socket,gs_valid_pia(OysterString))) :-
	!,
	write('Rule invoked: gs_valid_pia'),nl,
	write('PROLOG Input:  '),write(OysterString),nl,
	gs_valid(pia,OysterString,LClamString),
	write('PROLOG Output: '),write(LClamString),nl,
%	nl,write('< '),write(LClamString),nl,
	current_output(CO),
	tcp_output_stream(Socket, O),
	set_output(O),
	write(LClamString),put(10),
	flush_output(O),set_output(CO),
	write('Disconnected. Waiting for request...'),nl,
	ttyflush,
	tcp_shutdown(Socket).

dispatch(term(Socket,gs_cooper(OysterString))) :-
	!,
	write('Rule invoked: gs_cooper'),nl,
	write('PROLOG Input:  '),write(OysterString),nl,
	gs_cooper(pia,OysterString,LClamString),
	write('PROLOG Output: '),write(LClamString),nl,
%	nl,write('< '),write(LClamString),nl,
	current_output(CO),
	tcp_output_stream(Socket, O),
	set_output(O),
	write(LClamString),put(10),
	flush_output(O),set_output(CO),
	write('Disconnected. Waiting for request...'),nl,
	ttyflush,
	tcp_shutdown(Socket).

dispatch(term(Socket,gs_hodes(OysterString))) :-
	!,
	write('Rule invoked: gs_hodes'),nl,
	write('PROLOG Input:  '),write(OysterString),nl,
	gs_hodes(pia,OysterString,LClamString),
	write('PROLOG Output: '),write(LClamString),nl,
%	nl,write('< '),write(LClamString),nl,
	current_output(CO),
	tcp_output_stream(Socket, O),
	set_output(O),
	write(LClamString),put(10),
	flush_output(O),set_output(CO),
	write('Disconnected. Waiting for request...'),nl,
	ttyflush,
	tcp_shutdown(Socket).

dispatch(term(Socket,gs_solve_pia(OysterString))) :-
	!,
	write('Rule invoked: gs_solve_pia'),nl,
	write('PROLOG Input:  '),write(OysterString),nl,
	gs_solve(pia,OysterString,LClamString),
	write('PROLOG Output: '),write(LClamString),nl,
%	nl,write('< '),write(LClamString),nl,
	current_output(CO),
	tcp_output_stream(Socket, O),
	set_output(O),
	write(LClamString),put(10),
	flush_output(O),set_output(CO),
	write('Disconnected. Waiting for request...'),nl,
	ttyflush,
	tcp_shutdown(Socket).



dispatch(term(Socket,gs_simpl_pia(OysterString))) :-
	!,
	write('Rule invoked: gs_simpl_pia'),nl,
	write('PROLOG Input:  '),write(OysterString),nl,
	gs_simpl_pia(OysterString,LClamString),
	write('PROLOG Output: '),write(LClamString),nl,
%	nl,write('< '),write(LClamString),nl,
	current_output(CO),
	tcp_output_stream(Socket, O),
	set_output(O),
	write(LClamString),put(10),
	flush_output(O),set_output(CO),
	write('Disconnected. Waiting for request...'),nl,
	ttyflush,
	tcp_shutdown(Socket).



dispatch_term(T,C) :-
	current_output(CO),
	tcp_output_stream(C, O),
	set_output(O),
	write('hello'),put(10),
	flush_output(O),set_output(CO),
	write(T),nl,write(C),nl,
	ttyflush.

