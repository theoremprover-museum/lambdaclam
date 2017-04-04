module analytica.

accumulate maple.

type real osyn.

is_otype analytica real nil nil.

has_otype analytica onehalf nat.

has_otype analytica zero real.
has_otype analytica one real.
has_otype analytica two real.
has_otype analytica three real.
has_otype analytica four real.
has_otype analytica five real.
has_otype analytica six real.
has_otype analytica seven real.
has_otype analytica eight real.
has_otype analytica ten real.

has_otype analytica plus   ((tuple_type [real, real]) arrow real).
has_otype analytica minus  ((tuple_type [real, real]) arrow real).
has_otype analytica otimes ((tuple_type [real, real]) arrow real).
has_otype analytica odiv   ((tuple_type [real, real]) arrow real).
has_otype analytica exp    ((tuple_type [real, real]) arrow real).

has_otype analytica nat_to_real (nat arrow real).

has_otype analytica sqrt (real arrow real).

has_otype analytica fibonacci (nat arrow real).

has_otype analytica summation ((tuple_type [nat, nat, (nat arrow nat)]) arrow nat).

has_otype analytica summation ((tuple_type [nat, nat, (nat arrow real)]) arrow real).

%% the OpenMath phrasebook entries for the symbols:
%%================================================
print_open_math_ onehalf "'OMA'('OMS'(name: \"divide\" cd: \"arith1\") ['OMI'(1) 'OMI'(2)])".
print_open_math_ zero   "'OMI'(0)".
print_open_math_ one    "'OMI'(1)".
print_open_math_ two    "'OMI'(2)".
print_open_math_ three  "'OMI'(3)".
print_open_math_ four   "'OMI'(4)".
print_open_math_ five   "'OMI'(5)".
print_open_math_ six    "'OMI'(6)".
print_open_math_ seven  "'OMI'(7)".
print_open_math_ eight  "'OMI'(8)".
print_open_math_ nine   "'OMI'(9)".
print_open_math_ ten    "'OMI'(10)".

print_open_math_ plus   "'OMS'(name: \"plus\"  cd: \"arith1\")".
print_open_math_ minus  "'OMS'(name: \"minus\" cd: \"arith1\")".
print_open_math_ otimes "'OMS'(name: \"times\" cd: \"arith1\")".
print_open_math_ odiv   "'OMS'(name: \"divide\"   cd: \"arith1\")".
print_open_math_ exp    "'OMS'(name: \"power\" cd: \"arith1\")".
print_open_math_ sqrt   "'OMS'(name: \"sqrt\" cd: \"arith1\")".

%print_open_math_ summation "'OMS'(name: \"sum\"  cd: \"arith1\")".
print_open_math_ fibonacci "'OMS'(name: \"fibonacci\"  cd: \"arith1\")".

print_open_math_ (app summation (tuple [L, U, F])) Result:-
        print_open_math L LowerBound,
        print_open_math U UpperBound, 
        print_open_math F Function, 
        Result is "'OMA'('OMS'(name: \"sum\"  cd: \"arith1\") ['OMA'('OMS'(name: \"integer_interval\" cd: \"interval1\") [" ^ LowerBound ^ " " ^ UpperBound ^ "]) " ^ Function ^ "])".

print_open_math_ (app nat_to_real X) String:-
        print_open_math X String.


%% the definition of the fibonacci function
%%================================================
definition analytica fib_def_zero
           trueP
       (app fibonacci zero)
       zero.

definition analytica fib_def_one
           trueP
       (app fibonacci (app s zero))
       one.

definition analytica fib_def
           trueP
       (app fibonacci (app s (app s N)))
       (app plus (tuple [(app fibonacci N),
                         (app fibonacci (app s N))])).

definition analytica eq_refl trueP (app eq (tuple [X, X])) trueP.


%% example theorem from Analytica Tech Report
%%================================================
%%                              n              n
%%                  ((1+sqrt(5))  - (1-sqrt(5)) )
%% \forall n. F(n)= ------------------------------
%%                         (2^n * sqrt(5))
%%

top_goal analytica fib_goal []
        (app forall (tuple [nat, 
        (abs n\ (app eq 
         (tuple [(app fibonacci n),
                 (app odiv 
                    (tuple [(app minus 
                              (tuple [
                                 (app exp
                                    (tuple [(app plus  (tuple [one, (app sqrt five)])),
                                            (app nat_to_real n)])),
                                 (app exp 
                                    (tuple [(app minus (tuple [one, (app sqrt five)])),
                                            (app nat_to_real n)]))])),
                            (app otimes 
                               (tuple [(app exp (tuple [two, (app nat_to_real n)])),
                                       (app sqrt five)]))
                           ]))
                ])))])).


%% the induction scheme for fibonacci
%%================================================
%%
%%     P(0) /\ P(1) /\ forall n. (P(n) /\ P(s(n)) -> P(s(s(n))))   
%%   -----------------------------------------------------------
%%              forall n. P(n)
%%
%% almost like twostep in arithmetic.mod, but with both base cases in the hyps.
%%
induction_scheme analytica twostep2
   nat
   (dom (a\ (repl a (app s (app s a)))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [nat, (abs Prop)]))))
   (
    % Step cases
    (allGoal nat n\ (seqGoal (((hyp (otype_of n nat) nha)::
                               (hyp (Prop (app s n)) ind_hyp)::(hyp (Prop n) ind_hyp)::H)
			   >>>
			   (Prop (app s (app s n))))))
    % Base case
    **
      ((seqGoal (H >>> (Prop zero))) **
       (seqGoal (H >>> (Prop (app s zero)))))
	).



%% definition of summation function
%%================================================
%%
%%        n
%%      -----
%%      \         
%%       )   (F i)  = summation(0,n,F)
%%      /
%%      -----
%%      i = 0

definition analytica summation_zero
           trueP
       (app summation (tuple [zero, zero, (abs F)]))
       (F zero).

definition analytica summation_succ
           trueP
       (app summation (tuple [zero, (app s X), (abs F)]))
       (app plus (tuple [(app summation (tuple [zero, X, (abs F)])),
                         (F (app s X))])).

definition analytica summation_plus
           trueP
       (app summation (tuple [X, Y, (abs Z\ (app plus (tuple [(L Z), (R Z)])))]))
       (app plus (tuple [(app summation (tuple [X, Y, (abs Z\ (L Z))])),
                         (app summation (tuple [X, Y, (abs Z\ (R Z))]))])).

%% example taken from Analytica again
%%================================================
%% m <> 1 => forall n.
%%        n
%%      -----     k                    n+1
%%      \        2          1         2
%%       )    --------  = ----- + ----------
%%      /     1+m^(2^k)    m-1    1-m^(2^(n+1))
%%      -----
%%      i = 0
%%
%% Note:   

type m osyn.
has_otype analytica m nat.

top_goal analytica sum_ana [(app neg (app eq (tuple [m, (app s zero)])))]
        (app forall (tuple [nat, 
        (abs n\ 
         (app eq 
         (tuple [(app summation (tuple [zero, n, (abs x\ (app odiv (tuple [(app exp (tuple [two, x])), 
                                    (app plus (tuple [one, (app exp (tuple [m, (app exp (tuple [two, x]))]))]))])))])),
                 (app plus
                     (tuple [(app odiv 
                                 (tuple [one, 
                                   (app minus (tuple [m, one]))])),
                             (app odiv 
                                 (tuple [(app exp (tuple [two, (app s n)])),
                                         (app minus 
                                           (tuple [one, 
                                             (app exp (tuple [m, (app exp (tuple [two, (app s n)]))]))]))]))
                            ]))])))])).

%> simplify( 1/(1+m) = 1/(-1+m) + 2/(1-m^2) );
%                                       1       1
%                                     ----- = -----
%                                     1 + m   1 + m
%> simplify( (2*2^n)/(1+m^(2*2^n)) + 1/(-1+m) +  (2*2^n)/(1-m^(2*2^n)) = 1/(-1+m) + 4*2^n/(1-m^(4*2^n)) );
% does not work properly in Maple... 

%> simplify( (2*2^n)/(1+m^(2*2^n)) + 1/(-1+m)\                                          
%>  +  (2*2^n)/(1-m^(2*2^n)) = 1/(-1+m) + 4*2^n/(1-m^(4*2^n)) );
%                                        n                                           n
%                n         n         (4 2 )                  n         n         (4 2 )
%            -4 2  + 4 m~ 2  + 1 - m~                    -4 2  + 4 m~ 2  + 1 - m~
% - ------------------------------------------------ = - ------------------------------
%   /        (1 + n) \           /         (1 + n) \                 /           n \
%   |      (2       )|           |       (2       )|                 |       (4 2 )|
%   \1 + m~          / (-1 + m~) \-1 + m~          /       (-1 + m~) \-1 + m~      /

%> convert(simplify( (2*2^n)/(1+m^(2*2^n)) + \                                          
%> 1/(-1+m) +  (2*2^n)/(1-m^(2*2^n)) = 1/(-1+m) + 4*2^n/(1-m^(4*2^n)) ), string);
%"-(-4*2^n+4*m*2^n+1-m^(4*2^n))/(1+m^(2^(1+n)))/(-1+m)/(-1+m^(2^(1+n))) = -(-4*2^n+4\
%    *m*2^n+1-m^(4*2^n))/(-1+m)/(-1+m^(4*2^n))"


end

