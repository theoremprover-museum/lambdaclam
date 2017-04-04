% ***************************************************
%    Hodes' and Cooper's procedure 
%    PJ 
%
%    01.05.1998 
% ***************************************************


% ********************************************************************
% dp(+DP,+F,?A) runs Cooper's (DP=cooper) or Hodes'(DP=hodes) decision
% procedure for Presburger Arithmetic. Cooper's procedure is sound and
% complete for Presburger Integer Arithmetic. Hodes procedure is sound
% and complete for Presburger Real Arithmetic; it is sound, but
% INCOMPLETE for Presburger Integer Arithmetic.
% If a formula F is proved valid by a chosen procedure then
% A=yes, otherwise A=no
% ********************************************************************


dp_pia(DP,F,A) :-
   in_presburger_arithmetic(F,pnat),
   p_universal(F),
   dp_pia_(DP,F,F1),
%  nl,write('R:'),write(F1),
   (valid_pia(F1) -> A = {true}; A= void).

in_presburger_arithmetic(_,_).  % yet to be done 
p_universal(_).                 % yet to be done 

dp_pia_(DP,F,FF):-
   stratify_pia([_=>void,\,#],[_:_=>_,_:_#_],F,F1), % prenex normal form 
   remove_pia(s,F1,F2),                             % eliminate s(_)s
   remove_pia(=>,F2,F3),                            % eliminate =>s
   remove_pia(greater,F3,F4),                       % eliminate >s
   remove_pia(less,F4,F5),                          % eliminate less-s
   remove_pia(geq,F5,F6),                           % eliminate geqs
   eliminate_all_quantifiers(DP,F6,FF).

dp_pia_once(DP,F,AA) :-
   in_presburger_arithmetic(F,pnat),
   p_universal(F),
   dp_pia_once_(DP,F,A1),
   simplify_pia(A1,1,AA).

dp_simplify(F,[],F). % :- simplify(F,1,F1).
dp_simplify(F,[V:pnat|Vl],FF):- !,simplify_pia(F,V,F1),dp_simplify(F1,Vl,FF).
dp_simplify(F,[_|Vl],FF):- dp_simplify(F,Vl,FF).


dp_pia_once_(DP,F,FF):-
   stratify_pia([_=>void,\,#],[_:_=>_,_:_#_],F,F1),  % prenex normal form 
   remove_pia(s,F1,F2),                              % eliminate s(_)s
   remove_pia(=>,F2,F3),                             % eliminate =>s
   remove_pia(greater,F3,F4),                        % eliminate >s
   remove_pia(less,F4,F5),                           % eliminate less-s
   remove_pia(geq,F5,F6),                            % eliminate geqs
   eliminate_innermost_quantifier(DP,F6,FF).
          
eliminate_all_quantifiers(_,F,FF):-
   quantifier_free(F),!,simplify_pia(F,1,FF).
eliminate_all_quantifiers(DP,F,FF):-
   eliminate_innermost_quantifier(DP,F,F1),
   eliminate_all_quantifiers(DP,F1,FF).

eliminate_innermost_quantifier(DP,V:_#F,FF):-
   quantifier_free(F),!,
   eliminate_var(DP,V,F,F1),
%                                        handle just pnats instead of ints
%   eliminate_var(DP,V,leq(0,V)=>F,F1),  note the leq(0,V)=> hack to
%                                        handle just pnats instead of ints
   simplify_pia(F1,1,FF).
eliminate_innermost_quantifier(DP,V:T#F,V:T#F1):-
   eliminate_innermost_quantifier(DP,F,F1),!.
eliminate_innermost_quantifier(DP,V:_=>F,FF):-
   quantifier_free(F),!,eliminate_var(DP,V,F=>void,F1),
   simplify_pia(F1=>void,1,FF).
eliminate_innermost_quantifier(DP,V:T=>F,V:T=>F1):-
   eliminate_innermost_quantifier(DP,F,F1),!.
eliminate_innermost_quantifier(_,F,F).

quantifier_free(_:_=>_):-!,fail.
quantifier_free(_:_#_):-!,fail.
quantifier_free(F):-F=..[_,F1,F2],quantifier_free(F1),quantifier_free(F2),!.
quantifier_free(F):-F=..[_,F1],quantifier_free(F1),!.
quantifier_free(_).

% *********************************************
% from this point -- predicate eliminate_var/4
% cooper's and hodes' procedures differ
% *********************************************

eliminate_var(hodes,V,F,FF):-
   stratify_pia([_=>void],[\,#],F,F1),  
   thin_pia(_=>void,F1,F2),                          
   remove_pia(_=>void,F2,F3),
   stratify_pia([#],[\],F3,F4),
   isolate_pia(V,F4,F5),
   elim1(V,F5,FF).

eliminate_var(cooper,V,F,F7\F8):-
   remove_pia(=,F,F1),
   stratify_pia([_=>void],[\,#],F1,F2),
   thin_pia(_=>void,F2,F3),                          
   remove_pia(_=>void,F3,F4),  % stratify_pia([\],[#],F3,F4),
   isolate_pia(V,F4,F5),
   find_lcm_pia(V,F5,L),
   multiply(V,L,F5,F6),
   find_div_lcm_pia(V,F6#divisible(L,times(1,V)),LD),
   LD1 is LD-1,
   p_expand1(V,LD1,F6#divisible(L,times(1,V)),F7),
   expand2(V,LD1,F6#divisible(L,times(1,V)),F8).


% ***************************************************
%    Hodes' procedure
%    PJ 
%
%   26.04.1998 
% ***************************************************

elim1(V,F1\F2,FF):-elim1(V,F1,FF1),elim1(V,F2,FF2),simplify_pia(FF1\FF2,1,FF),!.
elim1(V,F,FF):- elim_from_disjunct(V,F,FF).

elim_from_disjunct(V,F,F):-  \+ (var_occurs(V,F)),!.
elim_from_disjunct(V,F,FF):- equality_occurs(V,F,Fe),
	!,elim_by_equality(V,F,Fe,FF).
elim_from_disjunct(V,F,FF):- p_pairing(V,F,F,FF).

var_occurs(V,F):- F=..[F0,A,B], member(F0,[leq,less,=]),
   (A=V;A=times(_,V);A=plus(_,V);A=plus(_,times(N,V));
   B=V;B=times(_,V);B=plus(_,V); B=plus(_,times(N,V))),!.
var_occurs(V,F):- F=..[_,F1,_], var_occurs(V,F1),!.
var_occurs(V,F):- F=..[_,_,F2], var_occurs(V,F2),!.
var_occurs(V,F):- F=..[_,F1], var_occurs(V,F1).

equality_occurs(V,times(N,V)=B in _pnat,times(N,V)=B in _pnat):- \+ (N=0),!.
equality_occurs(V,A=times(N,V) in _pnat,times(N,V)=A in _pnat):- \+ (N=0),!.
equality_occurs(V,F1#_,Fe):- equality_occurs(V,F1,Fe),!.
equality_occurs(V,_#F2,Fe):- equality_occurs(V,F2,Fe).


elim_by_equality(V,F1#F2,times(N,V)=T in _pnat,FF1#FF2):-
   elim_by_equality(V,F1,times(N,V)=T in _pnat,FF1),
   elim_by_equality(V,F2,times(N,V)=T in _pnat,FF2),!.
elim_by_equality(V,leq(times(M,V),T1),times(N,V)=T in _pnat,leq(times(M,T),times(N,T1))):-!.
elim_by_equality(V,leq(T1,times(M,V)),times(N,V)=T in _pnat,leq(times(N,T1),times(M,T))):-!.
elim_by_equality(V,times(M,V)=T1 in _pnat,times(N,V)=T in _pnat,times(M,T)=times(N,T1) in _pnat):-!.
elim_by_equality(V,T1=times(M,V) in _pnat,times(N,V)=T in _pnat,times(M,T1)=times(N,T) in _pnat):-!.
elim_by_equality(_,F,_,F).

%
% t1<n*x # m*x<t2 (and similar things) could be handled
% (in elim_by_equality/4 and pairing/4) n two ways:
% (a) m*t1<=n*t2
% (b) m1*t1<=n1*t2  where m1=lcm_pia(m,n)/m, n1=lcm_pia(m,n)/n
% the current choice is (a)
%

p_pairing(V,F1#F2,F,FF1#FF2):-p_pairing(V,F1,F,FF1),p_pairing(V,F2,F,FF2),!.
p_pairing(V,leq(T,times(N,V)),F1#F2,FF1#FF2):- p_pairing(V,leq(T,times(N,V)),F1,FF1),p_pairing(V,leq(T,times(N,V)),F2,FF2),!.
p_pairing(V,leq(T1,times(N,V)),leq(times(M,V),T2),leq(times(M,T1),times(N,T2))):-!.
p_pairing(V,leq(_,times(_,V)),_,leq(times(0,1),times(0,1))):-!.
p_pairing(V,leq(times(_,V),_),_,leq(times(0,1),times(0,1))):-!.
p_pairing(_,F,_,F).


% ***************************************************
%    Cooper's procedure
%    PJ 
%
%   01.05.1998 
% ***************************************************


find_lcm_pia(V,leq(times(N,V),_),N):-!.
find_lcm_pia(V,leq(_,times(N,V)),N):-!.
find_lcm_pia(V,divisible(_,plus(_,times(N,V))),N):-!.
find_lcm_pia(V,divisible(_,times(N,V)),N):-!.
find_lcm_pia(V,not_divisible(_,plus(_,times(N,V))),N):-!.
find_lcm_pia(V,not_divisible(_,times(N,V)),N):-!.

find_lcm_pia(V,F1#F2,L):-!,find_lcm_pia(V,F1,L1),find_lcm_pia(V,F2,L2),lcm_pia(L1,L2,L).
find_lcm_pia(V,F1\F2,L):-!,find_lcm_pia(V,F1,L1),find_lcm_pia(V,F2,L2),lcm_pia(L1,L2,L).
find_lcm_pia(_,_,1).

multiply(V,L,leq(times(N,V),T),leq(times(1,V),times(N1,T))):-!,N1 is L div N.
multiply(V,L,leq(T,times(N,V)),leq(times(N1,T),times(1,V))):-!,N1 is L div N.
multiply(V,L,divisible(U,plus(T,times(N,V))),divisible(UU,plus(times(N1,T),times(1,V)))):-
   !,(U=times(U0,1) -> UU is U0*(L div N); UU is U*(L div N)),N1 is L div N.
multiply(V,L,divisible(U,times(N,V)),divisible(UU,times(1,V))):-
   !,(U=times(U0,1) -> UU is U0*(L div N); UU is U*(L div N)).
multiply(V,L,not_divisible(U,plus(T,times(N,V))),not_divisible(UU,plus(times(N1,T),times(1,V)))):-
   !,(U=times(U0,1) -> UU is U0*(L div N); UU is U*(L div N)),N1 is L div N.
multiply(V,L,not_divisible(U,times(N,V)),not_divisible(UU,times(1,V))):-
   !,(U=times(U0,1) -> UU is U0*(L div N); UU is U*(L div N)).

multiply(V,L,F1#F2,FF1#FF2):-!,multiply(V,L,F1,FF1),multiply(V,L,F2,FF2).
multiply(V,L,F1\F2,FF1\FF2):-!,multiply(V,L,F1,FF1),multiply(V,L,F2,FF2).
multiply(_,_,F,F).

find_div_lcm_pia(V,divisible(L,plus(_,times(_,V))),L):-!.
find_div_lcm_pia(V,divisible(L,times(_,V)),L):-!.
find_div_lcm_pia(V,not_divisible(L,plus(_,times(_,V))),L):-!.
find_div_lcm_pia(V,not_divisible(L,times(_,V)),L):-!.

find_div_lcm_pia(V,F1#F2,L):-!,find_div_lcm_pia(V,F1,L1),find_div_lcm_pia(V,F2,L2),lcm_pia(L1,L2,L).
find_div_lcm_pia(V,F1\F2,L):-!,find_div_lcm_pia(V,F1,L1),find_div_lcm_pia(V,F2,L2),lcm_pia(L1,L2,L).
find_div_lcm_pia(_,_,1).

p_expand1(V,0,F,FF):-!,p_substitute(V,0,F,FF).
p_expand1(V,LD,F,F1\F2):-p_substitute(V,LD,F,F1),LD1 is LD-1,p_expand1(V,LD1,F,F2).

p_substitute(V,_,leq(times(1,V),_),leq(times(0,1),times(0,1))):-!.
p_substitute(V,_,leq(_,times(1,V)),leq(times(1,1),times(0,1))):-!.
p_substitute(V,C,divisible(N,times(1,V)),divisible(N,times(C,1))):-!.
p_substitute(V,C,divisible(N,plus(T,times(1,V))),divisible(N,plus(T,times(C,1)))):-!.
p_substitute(V,C,not_divisible(N,times(1,V)),not_divisible(N,times(C,1))):-!.
p_substitute(V,C,not_divisible(N,plus(T,times(1,V))),not_divisible(N,plus(T,times(C,1)))):-!.
p_substitute(V,C,F1#F2,FF1#FF2):-!,p_substitute(V,C,F1,FF1),p_substitute(V,C,F2,FF2).
p_substitute(V,C,F1\F2,FF1\FF2):-!,p_substitute(V,C,F1,FF1),p_substitute(V,C,F2,FF2).
p_substitute(_,_,F,F).

expand2(V,0,F,FF):-!,expand_by_b(V,0,F,F,FF).
expand2(V,LD,F,F1\F2):- expand_by_b(V,LD,F,F,F1),LD1 is LD-1,expand2(V,LD1,F,F2).

expand_by_b(V,J,leq(T,times(1,V)),F,FF):-!,substitute1(V,plus(T,times(J,1)),F,FF).
expand_by_b(V,J,F1#F2,F,FF1\FF2):-!,expand_by_b(V,J,F1,F,FF1),expand_by_b(V,J,F2,F,FF2).
expand_by_b(V,J,F1\F2,F,FF1\FF2):-!,expand_by_b(V,J,F1,F,FF1),expand_by_b(V,J,F2,F,FF2).
expand_by_b(_,_,_,_,leq(times(1,1),times(0,1))).

substitute1(V,C,leq(times(1,V),T),leq(times(1,C),T)):-!.
substitute1(V,C,leq(T,times(1,V)),leq(T,times(1,C))):-!.
substitute1(V,C,divisible(N,times(1,V)),divisible(N,times(1,C))):-!.
substitute1(V,C,divisible(N,plus(T,times(1,V))),divisible(N,plus(T,times(1,C)))):-!.
substitute1(V,C,not_divisible(N,times(1,V)),not_divisible(N,times(1,C))):-!.
substitute1(V,C,not_divisible(N,plus(T,times(1,V))),not_divisible(N,plus(T,times(1,C)))):-!.
substitute1(V,C,F1#F2,FF1#FF2):-!,substitute1(V,C,F1,FF1),substitute1(V,C,F2,FF2).
substitute1(V,C,F1\F2,FF1\FF2):-!,substitute1(V,C,F1,FF1),substitute1(V,C,F2,FF2).
substitute1(_,_,F,F).


