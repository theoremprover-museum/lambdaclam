% ***************************************************
%   Normalizators
%   PJ
%
%  16.04.1998   
% ***************************************************


% ************************************************************
% remove_pia(+R,+F1,?F2) removes occurences of function R (F2 is free of R)
% ************************************************************

remove_pia(s,s(A),plus(AA,1)):-!,remove_pia(s,A,AA).

remove_pia(=>,V:T=>A,V:T=>AA) :- !,remove_pia(=>,A,AA).
remove_pia(=>,A=>void,AA=>void) :- !,remove_pia(=>,A,AA).
remove_pia(=>,A=>B,(AA=>void)\BB):- !,remove_pia(=>,A,AA), remove_pia(=>,B,BB).

remove_pia(_=>void,less(A,B)=>void,less(B,plus(A,1)) ):- !.
remove_pia(_=>void,greater(A,B)=>void,greater(plus(B,1),A)):- !.
remove_pia(_=>void,leq(A,B)=>void,leq(plus(B,1),A)):- !.
remove_pia(_=>void,geq(A,B)=>void,geq(B,plus(A,1))):- !.
remove_pia(_=>void,divisible(A,B)=>void,not_divisible(A,B)):- !.
remove_pia(_=>void,not_divisible(A,B)=>void,divisible(A,B)):- !.

%remove_pia(_=>void,(A=B in _pnat)=>void,less(A,B)\less(B,A)):- !.
remove_pia(_=>void,(A=B in _pnat)=>void,leq(plus(A,1),B)\leq(plus(B,1),A)):- !.

remove_pia(=,T1=T2 in _pnat,leq(T1,T2)#leq(T2,T1)):-!.
remove_pia(geq,geq(T1,T2),leq(T2,T1)):-!.
remove_pia(leq,leq(T1,T2),less(T1,plus(T2,1))):-!.
remove_pia(greater,greater(T1,T2),leq(plus(T2,1),T1)):-!.
remove_pia(less,less(T1,T2),leq(plus(T1,1),T2)):-!.

remove_pia(R,F1,F2):- F1=..[F,A,B],remove_pia(R,A,AA),remove_pia(R,B,BB),F2=..[F,AA,BB],!.
remove_pia(R,F1,F2):- F1=..[F,A],remove_pia(R,A,AA),F2=..[F,AA],!.
remove_pia(_,F,F).



% ************************************************************
% thin_pia(+R,+F1,?F2) removes double occurences of function R
% (F2 is free of double occurences of R)
% ************************************************************

thin_pia(_=>void,(A=>void)=>void,AA) :- !,thin_pia(_=>void,A,AA).

thin_pia(R,F1,F2):- F1=..[F,A,B],thin_pia(R,A,AA),thin_pia(R,B,BB),F2=..[F,AA,BB],!.
thin_pia(R,F1,F2):- F1=..[F,A],thin_pia(R,A,AA),F2=..[F,AA],!.
thin_pia(_,F,F).



% ************************************************************
% stratify_pia(+L1,+L2,+F1,?F2) moves functions from L1 beneath functions from L2
% ************************************************************

stratify_pia(L1,L2,(V:T=>F)=>void,V:T#F1):-
        member(_=>void,L1),member(_:_=>_,L2),stratify_pia(L1,L2,F=>void,F1),!.
stratify_pia(L1,L2,(V:T#F)=>void,V:T=>F1):-
        member(_=>void,L1),member(_:_#_,L2),stratify_pia(L1,L2,F=>void,F1),!.
stratify_pia(L1,L2,(V:T=>F1)#F2,V:T=>F3):-
        member(#,L1),member(_:_=>_,L2),stratify_pia(L1,L2,F1#F2,F3),!.
stratify_pia(L1,L2,(V:T#F1)#F2,V:T#F3):- 
        member(#,L1),member(_:_#_,L2),stratify_pia(L1,L2,F1#F2,F3),!.
stratify_pia(L1,L2,(V:T=>F1)\F2,V:T=>F3):-
        member(\,L1),member(_:_=>_,L2),stratify_pia(L1,L2,F1\F2,F3),!.
stratify_pia(L1,L2,(V:T#F1)\F2,V:T#F3):-
        member(\,L1),member(_:_#_,L2),stratify_pia(L1,L2,F1\F2,F3),!.
stratify_pia(L1,L2,F1#(V:T=>F2),V:T=>F3):-
        member(#,L1),member(_:_=>_,L2),stratify_pia(L1,L2,F1#F2,F3),!.
stratify_pia(L1,L2,F1#(V:T#F2),V:T#F3):-
        member(\,L1),member(_:_#_,L2),stratify_pia(L1,L2,F1#F2,F3),!.
stratify_pia(L1,L2,F1\(V:T=>F2),V:T=>F3):-
        member(\,L1),member(_:_=>_,L2),stratify_pia(L1,L2,F1\F2,F3),!.
stratify_pia(L1,L2,F1\(V:T#F2),V:T#F3):-
        member(\,L1),member(_:_#_,L2),stratify_pia(L1,L2,F1\F2,F3),!.

stratify_pia(L1,L2,(F1#F2)=>void,FF1\FF2):-
	member(_=>void,L1),member(#,L2),
        stratify_pia(L1,L2,F1=>void,FF1),
	stratify_pia(L1,L2,F2=>void,FF2),!.
stratify_pia(L1,L2,(F1\F2)=>void,FF1#FF2):- member(_=>void,L1),member(\,L2),
        stratify_pia(L1,L2,F1=>void,FF1),stratify_pia(L1,L2,F2=>void,FF2),!.

stratify_pia(L1,L2,F1\(F2#F3),F12#F13):- member(\,L1),member(#,L2),
        stratify_pia(L1,L2,F1\F2,F12),stratify_pia(L1,L2,F1\F3,F13),!.
stratify_pia(L1,L2,(F2#F3)\F1,F12#F13):- member(\,L1),member(#,L2),
        stratify_pia(L1,L2,F2\F1,F12),stratify_pia(L1,L2,F3\F1,F13),!.

stratify_pia(L1,L2,F1#(F2\F3),F12\F13):- member(#,L1),member(\,L2),
        stratify_pia(L1,L2,F1#F2,F12),stratify_pia(L1,L2,F1#F3,F13),!.
stratify_pia(L1,L2,(F2\F3)#F1,F12\F13):- member(#,L1),member(\,L2),
        stratify_pia(L1,L2,F2#F1,F12),stratify_pia(L1,L2,F3#F1,F13),!.

stratify_pia(L1,L2,times(plus(T1,T2),T3),plus(TT1,TT2)):- member(times,L1),member(plus,L2),
        stratify_pia(L1,L2,times(T1,T3),TT1),stratify_pia(L1,L2,times(T2,T3),TT2),!.
stratify_pia(L1,L2,times(T3,plus(T1,T2)),plus(TT1,TT2)):- member(times,L1),member(plus,L2),
        stratify_pia(L1,L2,times(T3,T1),TT1),stratify_pia(L1,L2,times(T3,T2),TT2),!.

stratify_pia(L1,L2,V:T=>F,V:T=>FF):- stratify_pia(L1,L2,F,FF),!.
stratify_pia(L1,L2,V:T#F,V:T#FF):- stratify_pia(L1,L2,F,FF),!.

stratify_pia(L1,L2,F,FF):- F=..[F0,A,B],stratify_pia(L1,L2,A,AA),stratify_pia(L1,L2,B,BB),
        F1=..[F0,AA,BB],not(F=F1),!,stratify_pia(L1,L2,F1,FF).
stratify_pia(L1,L2,F,FF):- F=..[F0,A],stratify_pia(L1,L2,A,AA),
        F1=..[F0,AA],not(F=F1),!,stratify_pia(L1,L2,F1,FF).
stratify_pia(_,_,F,F).



% ************************************************************
% left_assoc_pia(+R,+F1,?F2) converts F1 into left associative form
% in respect to a function R 
% ************************************************************

left_assoc_pia(plus,plus(A,plus(B,C)),T):-left_assoc_pia(plus,plus(plus(A,B),C),T),!.

left_assoc_pia(times,times(A,times(B,C)),T):-N is A*B,left_assoc_pia(times,times(N,C),T),!.

left_assoc_pia(R,F1,F2):- F1=..[F,A,B],left_assoc_pia(R,A,AA),left_assoc_pia(R,B,BB),F2=..[F,AA,BB],!.
left_assoc_pia(R,F1,F2):- F1=..[F,A],left_assoc_pia(R,A,AA),F2=..[F,AA],!.
left_assoc_pia(_,F,F).



% **********************************************************************
% reorder_pia(+V,+F1,?F2) moves Vs and times(_,V)s at the end of the formula F1
% (the partial ordering used is number<V and U<V for every variable)
% **********************************************************************


reorder_pia(V,plus(plus(A,B),C),T):- reorder_pia(V,plus(A,B),plus(AA,BB)),
    ((BB=V;BB=times(_,V)),not(C=V),not(C=times(_,V)) ->
    (reorder_pia(V,plus(AA,C),T1),T=plus(T1,BB) ); T=plus(plus(AA,BB),C) ),!.
reorder_pia(V,plus(A,B),plus(B,A)):-(A=V;A=times(_,V)),not(B=V),not(B=times(_,V)),!.
reorder_pia(V,F1,F2):- F1=..[F,A,B],reorder_pia(V,A,AA),reorder_pia(V,B,BB),F2=..[F,AA,BB],!.
reorder_pia(V,F1,F2):- F1=..[F,A],reorder_pia(V,A,AA),F2=..[F,AA],!.
reorder_pia(_,F,F).


% ************************************************************
% poly_form_pia(+T1,?T2) converts terms into linear normal form:
% t :=t+t|t'
% t':=int'*var|int'*1
% (when possible, we eliminate factors 0*V)
% ************************************************************

poly_form_pia(plus(A,times(N,V)),AA):-(N=0;V=0),!,poly_form_pia(A,AA).
poly_form_pia(plus(times(N,V),A),AA):-(N=0;V=0),!,poly_form_pia(A,AA).
poly_form_pia(plus(N,M),times(N1,1)):-number(N),number(M),N1 is N+M,!.
poly_form_pia(times(N,V),times(0,1)):-(N=0;V=0),!.
poly_form_pia(times(N,1),times(N,1)):- !.
poly_form_pia(times(N,V),times(N1,1)):- number(V),!,N1 is N*V.
poly_form_pia(V,times(V,1)):-number(V),!.
poly_form_pia(times(N,V),times(N,V)):- !.
%poly_form_pia(V,times(1,V)):-atom(V),!.
poly_form_pia(V:T=>F,V:T=>FF):-poly_form_pia(F,FF),!.   % not very nice; 
poly_form_pia(V:T#F,V:T#FF):-poly_form_pia(F,FF),!.     % this has to be done because of the next clause
poly_form_pia(V,times(1,V)):- atom(V),\+ (V=pnat), \+ (V=void), \+ (V=true),!.


poly_form_pia(divisible(A,B),divisible(AA,BB)):-!,poly_form_pia(A,AA),poly_form_pia(B,BB).
poly_form_pia(not_divisible(A,B),not_divisible(AA,BB)):-!,poly_form_pia(A,AA),poly_form_pia(B,BB).
poly_form_pia(leq(A,B),leq(AA,BB)):-!,poly_form_pia(A,AA),poly_form_pia(B,BB).
poly_form_pia(less(A,B),less(AA,BB)):-!,poly_form_pia(A,AA),poly_form_pia(B,BB).
poly_form_pia(A=B in _pnat,AA=BB in _pnat):-!,poly_form_pia(A,AA),poly_form_pia(B,BB).

poly_form_pia(F1,F2):- F1=..[F,A,B],poly_form_pia(A,AA),poly_form_pia(B,BB),F2=..[F,AA,BB],!.
poly_form_pia(F1,F2):- F1=..[F,A],poly_form_pia(A,AA),F2=..[F,AA],!.
poly_form_pia(F,F).


% ************************************************************
% collect_pia(+V,+T1,?T2) collect_pias occurences of V and of times(_,V)
% assumes that 
%  - 'times's are beneath 'plus's.
%  - T1 is in left associative form
%  - all occurences of times(_,V) are at the end of the term T1
% which can be done using
%  - stratify_pia([times],[plus],F,F1)
%  - left_assoc_pia(plus,F1,F2)
%  - poly_form_pia(F2,F3)
%  - reorder_pia(V,F3,F4)
% T2 is either of the form plus(_,times(N,V)) or of the form times(N,V)
% ************************************************************


collect_pia(V,plus(plus(A,times(N,V)),times(M,V)),AA):-(N+M)=:=0,!,collect_pia(V,A,AA),!.
collect_pia(V,plus(plus(A,times(N,V)),times(M,V)),AA):-!,N1 is N+M,collect_pia(V,plus(A,times(N1,V)),AA).
collect_pia(V,plus(times(N,V),times(M,V)),times(0,1)):- 0=:=N+M,!.
collect_pia(V,plus(times(N,V),times(M,V)),times(N1,V)):- N1 is N+M,!.
collect_pia(V,plus(A,times(N,V)),T):- collect_pia(V,A,AA),not(A=AA),!,collect_pia(V,plus(AA,times(N,V)),T).

collect_pia(V,F1,F2):- F1=..[F,A,B],collect_pia(V,A,AA),collect_pia(V,B,BB),F2=..[F,AA,BB],!.
collect_pia(V,F1,F2):- F1=..[F,A],collect_pia(V,A,AA),F2=..[F,AA],!.
collect_pia(_,F,F).



% ************************************************************
% isolate_pia(+V,+F1,?F2) isolates variable V
% ************************************************************

isolate_pia(V,less(T1,T2),F):-
    (T1=0 -> TT1=T2; TT1=plus(T2,times(-1,T1))),
    stratify_pia([times],[plus],TT1,TT2),
    left_assoc_pia(times,TT2,TT3),
    left_assoc_pia(plus,TT3,TT4),
    poly_form_pia(TT4,TT5),
    reorder_pia(V,TT5,TT6),
    collect_pia(V,TT6,TT7),
    isolate1(V,less(0,TT7),F),!.

isolate_pia(V,leq(T1,T2),F):-
    (T1=0 -> TT1=T2; TT1=plus(T2,times(-1,T1))),
    stratify_pia([times],[plus],TT1,TT2),
    left_assoc_pia(times,TT2,TT3),
    left_assoc_pia(plus,TT3,TT4),
    poly_form_pia(TT4,TT5),
    reorder_pia(V,TT5,TT6),
    collect_pia(V,TT6,TT7),
    isolate1(V,leq(0,TT7),F),!.

isolate_pia(V,T1=T2 in _pnat,F):-
    (T1=0 -> TT1=T2; TT1=plus(T2,times(-1,T1))),
    stratify_pia([times],[plus],TT1,TT2),
    left_assoc_pia(times,TT2,TT3),
    left_assoc_pia(plus,TT3,TT4),
    poly_form_pia(TT4,TT5),
    reorder_pia(V,TT5,TT6),
    collect_pia(V,TT6,TT7),
    isolate1(V,0=TT7 in _pnat,F),!.

isolate_pia(V,divisible(N,T1),divisible(N,T7)):-!,
    stratify_pia([times],[plus],T1,T2),
    left_assoc_pia(times,T2,T3),
    left_assoc_pia(plus,T3,T4),
    poly_form_pia(T4,T5),
    reorder_pia(V,T5,T6),
    collect_pia(V,T6,T7).

isolate_pia(V,not_divisible(N,T1),divisible(N,T7)):-!,
    stratify_pia([times],[plus],T1,T2),
    left_assoc_pia(times,T2,T3),
    left_assoc_pia(plus,T3,T4),
    poly_form_pia(T4,T5),
    reorder_pia(V,T5,T6),
    collect_pia(V,T6,T7).


isolate_pia(V,F1,F2):- F1=..[F,A,B],isolate_pia(V,A,AA),isolate_pia(V,B,BB),F2=..[F,AA,BB],!.
isolate_pia(V,F1,F2):- F1=..[F,A],isolate_pia(V,A,AA),F2=..[F,AA],!.
isolate_pia(_,F,F).

isolate1(V,less(0,plus(T1,times(N,V))),less(times(N1,V),T1)):-N<0,!,N1 is -N.
isolate1(V,less(0,plus(T1,times(N,V))),less(TT,times(N,V))):-
     stratify_pia([times],[plus],times(-1,T1),T2),left_assoc_pia(times,T2,T3),poly_form_pia(T3,TT),!.
isolate1(V,less(0,times(N,V)),less(times(1,V),times(0,1))):-N<0,!.
isolate1(V,less(0,times(N,V)),less(times(0,1),times(N,V))):-!.

isolate1(V,leq(0,plus(T1,times(N,V))),leq(times(N1,V),T1)):-N<0,!,N1 is -N.
isolate1(V,leq(0,plus(T1,times(N,V))),leq(TT,times(N,V))):-
     stratify_pia([times],[plus],times(-1,T1),T2),left_assoc_pia(times,T2,T3),poly_form_pia(T3,TT),!.
isolate1(V,leq(0,times(N,V)),leq(times(1,V),times(0,1))):-N<0,!.
isolate1(V,leq(0,times(N,V)),leq(times(0,1),times(N,V))):-!.

isolate1(V,0=plus(T1,times(N,V))in _pnat,times(N1,V)=T1 in _pnat):-N<0,!,N1 is -N.
isolate1(V,0=plus(T1,times(N,V))in _pnat,TT=times(N,V)in _pnat):-
     stratify_pia([times],[plus],times(-1,T1),T2),left_assoc_pia(times,T2,T3),poly_form_pia(T3,TT),!.
isolate1(V,0=times(N,V)in _pnat,times(1,V)=times(0,1) in _pnat):-N<0,!.
isolate1(V,0=times(N,V)in _pnat,times(0,1)=times(N,V)in _pnat):-!.

isolate1(_,F,F).


% *****************************************************
%  simplify and reduce
% *****************************************************



simplify_pia(F,V,FF):-
   stratify_pia([_=>void],[\,#],F,F1),
   thin_pia(_=>void,F1,F2),
   remove_pia(_=>void,F2,F3),
   stratify_pia([times],[plus],F3,F4),
   left_assoc_pia(times,F4,F5),
   left_assoc_pia(plus,F5,F6),
   poly_form_pia(F6,F7),
   reorder_pia(V,F7,F8),
   collect_pia(V,F8,F9),
   reduce_pia(F9,FF).

%reduce_pia(F1\_,leq(times(0,1),times(0,1))):-valid_pia(F1),!.
%reduce_pia(_\F2,leq(times(0,1),times(0,1))):-valid_pia(F2),!.
%reduce_pia(F1\F2,FF2):-invalid_pia(F1),!,reduce_pia(F2,FF2).
%reduce_pia(F1\F2,FF1):-invalid_pia(F2),!,reduce_pia(F1,FF1).
%reduce_pia(F1#F2,FF2):-valid_pia(F1),!,reduce_pia(F2,FF2).
%reduce_pia(F1#F2,FF1):-valid_pia(F2),!,reduce_pia(F1,FF1).
%reduce_pia(F1#_,leq(times(1,1),times(0,1))):-invalid_pia(F1),!.
%reduce_pia(_#F2,leq(times(1,1),times(0,1))):-invalid_pia(F2),!.
%reduce_pia(F,leq(times(0,1),times(0,1))):-valid_pia(F),!.
%reduce_pia(F,leq(times(1,1),times(0,1))):-invalid_pia(F),!.

reduce_pia(F1\_,{true}):-valid_pia(F1),!.
reduce_pia(_\F2,{true}):-valid_pia(F2),!.
reduce_pia(F1\F2,FF2):-invalid_pia(F1),!,reduce_pia(F2,FF2).
reduce_pia(F1\F2,FF1):-invalid_pia(F2),!,reduce_pia(F1,FF1).
reduce_pia(F1#F2,FF2):-valid_pia(F1),!,reduce_pia(F2,FF2).
reduce_pia(F1#F2,FF1):-valid_pia(F2),!,reduce_pia(F1,FF1).
reduce_pia(F1#_,void):-invalid_pia(F1),!.
reduce_pia(_#F2,void):-invalid_pia(F2),!.
reduce_pia(F,{true}):-valid_pia(F),!.
reduce_pia(F,void):-invalid_pia(F),!.
reduce_pia(F=>void,{true}):-invalid_pia(F),!.
reduce_pia(F=>void,void):-valid_pia(F),!.

reduce_pia(V:T#F,V:T#FF):-reduce_pia(F,FF),!.
reduce_pia(F#F,FF):- reduce_pia(F,FF),!.    %
reduce_pia(F\F,FF):- reduce_pia(F,FF),!.    % 14.12.1998.
reduce_pia(F1#F2,F):-reduce_pia(F1,FF1),reduce_pia(F2,FF2),
  ( (F1=FF1,F2=FF2) -> (F=(F1#F2)) ;(reduce_pia(FF1#FF2,F))),!.
reduce_pia(F1\F2,F):-reduce_pia(F1,FF1),reduce_pia(F2,FF2),
  ( (F1=FF1,F2=FF2) -> (F=(F1\F2)) ;(reduce_pia(FF1\FF2,F))),!.
reduce_pia(F,F).

valid_pia(leq(times(0,s(0)),times(0,s(0)))):-!.
valid_pia(leq(times(N,1),times(M,1))):-N=<M,!.
valid_pia(less(times(N,1),times(M,1))):-N<M,!.
valid_pia((times(N,1)=times(M,1)) in _pnat):-N=:=M,!.
valid_pia(divisible(times(N,1),_)):-(N=:=1;N=:=(-1)),!.
%valid_pia(divisible(N,_)):-number(N),(N=:=1;N=:=(-1)),!.
valid_pia(divisible(times(N,1),times(M,1))):-not(M=0),(M mod N)=:=0,!.
%valid_pia(divisible(N,times(M,1))):-number(N),not(M=0),(M mod N)=:=0,!.
valid_pia(divisible(_,times(0,_))):-!.
%valid_pia(not_divisible(N,times(M,1))):-number(N),not(M=0),(M mod N)=\=0,!.
valid_pia(not_divisible(times(N,1),times(M,1))):-not(M=0),(M mod N)=\=0,!.
valid_pia({true}).

invalid_pia(leq(times(s(0),s(0)),times(0,s(0)))):-!.
invalid_pia(leq(times(N,1),times(M,1))):-N>M,!.
invalid_pia(less(times(N,1),times(M,1))):-N>=M,!.
invalid_pia((times(N,1)=times(M,1)in _pnat)):-N=\=M,!.
%invalid_pia(not_divisible(N,times(M,1))):-number(N),not(M=0),(M mod N)=:=0,!.
invalid_pia(not_divisible(times(N,1),times(M,1))):-not(M=0),(M mod N)=:=0,!.
invalid_pia(not_divisible(times(N,1),_)):-(N=:=1;N=:=(-1)),!.
%invalid_pia(not_divisible(N,_)):-number(N),(N=:=1;N=:=(-1)),!.
invalid_pia(not_divisible(_,times(0,_))):-!.
invalid_pia(divisible(times(N,1),times(M,1))):-not(M=0),(M mod N)=\=0,!.
%invalid_pia(divisible(N,times(M,1))):-number(N),not(M=0),(M mod N)=\=0,!.
invalid_pia(void).


% ************************************************************
% p_cnf(+F1,?F2) converts F1 into the CNF 
% ************************************************************

p_cnf(F,FF):-
   remove_pia(=>,F,F1),                               % eliminate =>s
   stratify_pia([_=>void,\,#],[_:_=>_,_:_#_],F1,F2),  % prenex normal form 
   stratify_pia([_=>void],[\,#],F2,F3),               % move negations beneath \s and #s 
   thin_pia(_=>void,F3,F4),                           % eliminate multiple negations
   stratify_pia([\],[#],F4,FF).                       % move disjunctions beneath conjunctions


% ************************************************************
% p_lcm(+N1,+N2,?N3) 
% ************************************************************

lcm_pia(A,B,C):-gcd_pia(A,B,D),C is A*B // D.

gcd_pia(A,A,A):-!.
gcd_pia(A,B,B):-A>B,D is A mod B,D=0,!.
gcd_pia(A,B,C):-A>B,D is A mod B,not(D=0),gcd_pia(D,B,C),!.
gcd_pia(A,B,A):-A<B,D is B mod A,D=0,!.
gcd_pia(A,B,C):-A<B,D is B mod A,not(D=0),gcd_pia(D,A,C).
