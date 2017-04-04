/*
 *
 *  March 2000.  PJ
 *
 *  The module for constant congruence closure.
 *  Intended for use in general setting for incorporation
 *  of decision procedures.
 *  Congruence closure on ground equalities is basen on Nelson/Oppen algorithm.
 *  From each class, a representative is taken and
 *  all equalities are added to a formula being proved (which
 *  is conjunction of literals). The smallest element is choosen
 *  according to some ordering (there are one based on RPOS and one
 *  based on Boyer/Moore alphabetical ordering).
 *  All ground equalities are interreduced, and then all other
 *  literals are normalised
 */

ccc(Theories,F,Fr):- ccc_(Theories,F,Fr),
            \+ member((T=T in _)=>void,Fr), 
            \+ (member(A,Fr),member(A=>void,Fr)),!.
ccc(_Theories,_,[void]).

ccc_(Theories,F,Fr):-
            retractall(regccc(_)),
            retractall(eqsccc(_)),
            registry(positive,Tau,Prec,_),
            assert(regccc(Tau-Prec)),
            assert(eqsccc([])),
            make_list_ge(F,Fe),
            no_ccc(Theories,Fe),
            minimum_terms,
            interreduce,
            ccc_normalise(Theories,F,Fr).

ccc_normalise(Theories,[A=B in _|L],L1):-
      groundp(A),groundp(B),!,ccc_normalise(Theories,L,L1).
ccc_normalise(Theories,[Af|L],[Af1|L1]):-
      !,
      eqsccc(E),
      member(Theory,Theories),
      is_T_atomic_formula(Theory,Af),
      select_T_equalities(Theory,E,EE),
%nl,write(E),nl,write(Theory),write(' et'),write(EE),nl,
      canonical_form(Af,EE,Af1),
      ccc_normalise(Theories,L,L1).
ccc_normalise(_Theories,[],E1):- eqsccc(E),clear_eqnames(E,E1).

select_T_equalities(_Theory,[],[]).
select_T_equalities(Theory,[D:E|L],[D:E|LL]):-
      is_T_atomic_formula(Theory,E),!,
      select_T_equalities(Theory,L,LL).
select_T_equalities(Theory,[_|L],LL):-
      select_T_equalities(Theory,L,LL).


no_ccc(Theories,T):-
      retractall(use(_,_)),
      retractall(class(_,_)),
      assert(use(nil,nil)),
      assert(class(nil,nil)),
      makeuse(T),
      no_(T),
%nl,write('A:'),listing(class(_,_)),nl,
      findallclasses(L),
      separate(Theories,L)
%nl,write('B:'),listing(class(_,_)),nl
      .


findallclasses(L):- bagof(class(A,B),(class(A,B),\+ B=nil),L),!.
findallclasses([]).

separate(Theories,[class(A,C)|CL]):- 
                     separate_class(A,C,Theories,L),
                     remove_duplicates(L,L1),
                     retractall(class(A,C)),
                     add_new_classes(L1),
                     separate(Theories,CL).
separate(_Theories,[]).

separate_class(_A,_C,[],[]):-!.
separate_class(A,C,[T|Theories],LL):-
                     list_of_T_terms(T,C,C1),
                     ( (\+ C1=[],
%                     \+ C1=C,
                     C1=[B|_])
                     ->
                     append(L,[class(B,C1)],LL)
                     ;
                     LL=L ),
                     separate_class(A,C,Theories,L),!.

add_new_classes([]):-!.
add_new_classes([M|L]):- assert(M),add_new_classes(L).


list_of_T_terms(_,[],[]):-!.
list_of_T_terms(Theory,[L|LL],[L|LL1]):-
             are_T_terms(Theory,[L]),!,
             list_of_T_terms(Theory,LL,LL1).
list_of_T_terms(Theory,[_L|LL],LL1):-
             list_of_T_terms(Theory,LL,LL1).


remove_duplicates([],[]).
remove_duplicates([A|L],[A|LL]):-
             \+ member(A,L),!,
             remove_duplicates(L,LL).
remove_duplicates([_|L],LL):-
             remove_duplicates(L,LL).




% *********************************


ccc(F,Fr):- ccc_(F,Fr),
            \+ member((T=T in _)=>void,Fr), 
            \+ (member(A,Fr),member(A=>void,Fr)),!.
ccc(_,[void]).
% changed on 20.11.2000; this has some consequences both to SGS and to
% the first version of GS 


ccc_(F,Fr):- retractall(regccc(_)),
            retractall(eqsccc(_)),
%            registry(positive,Tau,Prec,_),
%            assert(regccc(Tau-Prec)),
	    assert(regccc(nil)), % no RPOS ordering available at the moment
	                         % only simple size ordering is used
            assert(eqsccc([])),
            make_list_ge(F,Fe),
            no_ccc(Fe),
            minimum_terms,
            interreduce,
            ccc_normalise(F,Fr).

make_list_ge([A=B in T|L],[A=B in T|L1]):-groundp(A),groundp(B),!,make_list_ge(L,L1).
make_list_ge([_|L],L1):-!,make_list_ge(L,L1).
make_list_ge([],[]).


interreduce:-
      eqsccc(E),
      interreduce_(E,E,E1),
      retract(eqsccc(E)),
      del_refl(E1,E2),
      del_multiples(E2,E3), % added 01.05.2001
      assert(eqsccc(E3)).

interreduce_(E,[_:(A=B in T)|L],[ccc:Af1|L1]):-
      delete(E,_:(A=B in T),Ed),
      canonical_form(A=B in T,Ed,Af1),
      interreduce_(E,L,L1).
interreduce_(_,[],[]).

del_refl([],[]).
del_refl([_:A=A in _|L],L1):-!,del_refl(L,L1).
del_refl([E|L],[E|L1]):-del_refl(L,L1).

del_multiples([],[]).
del_multiples([A|L],L1):- member(A,L),!,del_multiples(L,L1).
del_multiples([A|L],[A|L1]):- del_multiples(L,L1).


ccc_normalise([A=B in _|L],L1):-
      groundp(A),groundp(B),!,ccc_normalise(L,L1).
ccc_normalise([Af|L],[Af1|L1]):-
      !,
      eqsccc(E),
      canonical_form(Af,E,Af1),
      ccc_normalise(L,L1).
ccc_normalise([],E1):- eqsccc(E),clear_eqnames(E,E1).

clear_eqnames([_:Eq|L],[Eq|L1]):-clear_eqnames(L,L1).
clear_eqnames([],[]).
                           
minimum_terms:-class(_,C),not(C=nil),
               regccc(TP),
               minimum_term(C,Min,TP,TPNew),
               addeqs(C,Min),
               retract(regccc(TP)),
               assert(regccc(TPNew)),fail.
minimum_terms.

addeqs([M|C],M):-!,addeqs(C,M).
addeqs([M1|C],M):- eqsccc(E),
%                  type_of([],M1,T),
%                  append(E,[ccc:(M1=M in T)],E1),
% ! generally, sorts should be taken into account
% however, equality is not sorted in LambdaProlog, so
% it is not needed to follow old Clam's syntax in this.
% instead, we use only "generic_type" sort
                   append(E,[ccc:(M1=M in generic_type)],E1),
                   retract(eqsccc(E)),
                   assert(eqsccc(E1)),
                   addeqs(C,M).
addeqs([],_).


%this is based on RPOS ordering */
%minimum_term(C,Min,Tau-Prec,TPNew):-
%                     member(Min,C),
%                     checkallmembers(C,Min,Tau-Prec,TPNew),!.
%
%checkallmembers([M|C],M,Tau-Prec,TPNew):-
%                     !,checkallmembers(C,M,Tau-Prec,TPNew).
%checkallmembers([M1|C],M,Tau-Prec,TPNew):-
%                     (M1=M; rpos_prove(M1>M,Tau-Prec,NTP,[],_)),
%                     checkallmembers(C,M,NTP,TPNew).
%checkallmembers([],_,TP,TP).
%


% this is based on something like Boyer/Moore ordering 

minimum_term(C,Min,_,_):-
                     member(Min,C),
                     checkallmembers(C,Min),!.
checkallmembers([M|C],M):-
                     !,checkallmembers(C,M).
checkallmembers([M1|C],M):-
                     (M1=M;heavier_term(M1,M)),
                     checkallmembers(C,M).
checkallmembers([],_).


heavier_term(T1,T2):-size(T1,S1),size(T2,S2),S1>S2,!.
heavier_term(T1,T2):-size(T1,S1),size(T2,S2),S1<S2,!,fail.
heavier_term(T1,T2):-functor(T1,_,A1),functor(T2,_,A2),A1>A2,!.
heavier_term(T1,T2):-functor(T1,_,A1),functor(T2,_,A2),A1<A2,!,fail.
heavier_term(T1,T2):-functor(T1,F1,A),functor(T2,F2,A),heavier_lex(F1,F2),!.
heavier_term(T1,T2):-functor(T1,F1,A),functor(T2,F2,A),heavier_lex(F2,F1),!,fail.
heavier_term(T1,T2):-
	functor(T1,F,A),
	functor(T2,F,A),
	args(T1,A1),
	args(T2,A2),
	heavier_list(A1,A2),!.

heavier_list([],[]).
heavier_list([A|L1],[A|L2]):-heavier_list(L1,L2),!.
heavier_list([A1|_],[A2|_]):- heavier_term(A1,A2).
% fixed on 19.11.2000; the above two lines replaces the following three lines
%heavier_list([A1|_],[A2|_]):- \+ heavier_term(A1,A2),!,fail.
%heavier_list([A|L1],[A|L2]):-heavier_list(L1,L2),!.
%heavier_list([_|L1],[_|L2]):-heavier_list(L1,L2),!.

size(T,0):-atomic(T),!.
size(T,S):-args(T,Args),sum_all_sizes(Args,S1),S is S1+1.
sum_all_sizes([],0):-!.
sum_all_sizes([A|L],S):-size(A,S0),sum_all_sizes(L,S1),S is S0+S1.

heavier_lex(A,B):-name(A,An),name(B,Bn),after_lex(An,Bn).

after_lex([],[]):-!,fail.
after_lex([A|_],[B|_]):-A>B,!.
after_lex([A|Al],[A|Bl]):-after_lex(Al,Bl),!.
after_lex(_,[]):-!,fail.




/* **************  Nelson-Oppen congruence closure ************** */

merge(U,V):- unionuse(U,Pu),
             unionuse(V,Pv),
             unionclasses(U,V),
             check(Pu,Pv),!.

unionuse(U,Pv):-find(U,Fu),bagof(U1,(find(U1,Fu)),L),
                unionuse_(L,Pv).
unionuse(_,[]).

unionuse_([],[]).
unionuse_([U|L],L1):- (use(U,Lu) -> true ; Lu=[]),
                      unionuse_(L,L2),union(Lu,L2,L1).

check(Pu,Pv):-member(X,Pu),
              member(Y,Pv),
              find(X,Fx),find(Y,Fy),
              not(Fx=Fy),
              congruent(X,Y),
              merge(X,Y),
              fail.
check(_,_).


unionclasses(U,V):-class(R1,C1),member(U,C1),
                   class(R2,C2),member(V,C2),
                   retractall(class(R1,C1)),
                   retractall(class(R2,C2)),
                   union(C1,C2,C),
                   (exp_at(R1,_,R2)
                      -> assert(class(R2,C))
                      ;  assert(class(R1,C))),!.

congruent(U,V):-
                U=.. [F|Ul], V=.. [F|Vl],
                length(Ul,Du),length(Vl,Du),
                checkargs(U,V,Du),!.

checkargs(_,_,0).
checkargs(U,V,N):-N>0,arg(N,U,Au),arg(N,V,Av),
                  find(Au,FAu),find(Av,FAu),
                  N1 is N-1,
                  checkargs(U,V,N1).

no_ccc(T):-
      retractall(use(_,_)),
      retractall(class(_,_)),
      assert(use(nil,nil)),
      assert(class(nil,nil)),
      makeuse(T),
      no_(T).

no_([]).
no_([A=B in _|T]):-
               no_(T),
               find(A,Fa),
               find(B,Fb),!,
               ((Fa=Fb) -> true ; merge(A,B)).

%find(A,M):-class(AA,C),member(A,C), 
%           AA=..[F|Args],findargs(Args,Args1),M=..[F|Args1].

find(A,AA):-class(AA,C),member(A,C).
find(A,A):- \+ (class(_,C),member(A,C)).

findargs([],[]).
findargs([A|L],[A1|L1]):-!,find(A,A1),findargs(L,L1).

makeuse([]):-!.
makeuse([A=B in _|L]):-
                  makeuse(L),
                  processterm(A),
                  processterm(B),!.

processterm(A):- (class(_,C),
                  member(A,C)
                  -> true
                  ;  assert(class(A,[A]))),fail.
processterm(A):- atom(A),!.
processterm(A):- A=..[_|Args],processargs(A,Args).

processargs(_,[]).
processargs(A,[Arg|L]):-
                (use(Arg,U)
                 -> (retract(use(Arg,U)),
                     union(U,[A],U1),
                     assert(use(Arg,U1)))
                  ;  assert(use(Arg,[A]))),
                 processterm(Arg),
                 processargs(A,L).

/* End of Nelson-Oppen congruence closure */   

groundp(_).
% actually, grounp(X) has to check whether there is
% some meta-variable in the argument X.
% we assume that it is never the case.


args(T,Args) :- T=..[_|Args].

