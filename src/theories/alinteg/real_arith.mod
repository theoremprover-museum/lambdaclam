/*

File: real_arith.mod
Author: Alex Heneveld
Description: define real nums, arithmetic
Created: Oct 02 (based on work in Jan 00)

*/

module real_arith.

accumulate lxtest.
accumulate rewriting. %needed b/c rewrite_with_rules isn't visible otherwise

%
% -------------------- HELPERS ------------------------ 
%

% is_permut, true if the two lists are permutations of each other
is_permut A A.
is_permut (A :: B) (A :: C) :- is_permut B C.
is_permut (A :: B) (C :: D) :- 
  remove A D E,
  is_permut B (C :: E).

% remove obj src dest, removes obj from src, returns dest
remove A (A :: B) B.
remove A (C :: B) (C :: D) :-
  remove A B D.

remove_all A nil nil.
remove_all A (A :: B) C :- !, remove_all A B C.
remove_all A (B :: C) (B :: D) :- remove_all A C D.

append_lists nil nil nil.
append_lists (LAH::LAT) LB (LAH::LFT) :-
  append_lists LAT LB LFT.
append_lists nil LB LB.

list_contains (X :: _A) X.
list_contains (_A :: B) X :-
  list_contains B X.

% the unpack operator puts any embedded OP on the top level, ie
% OP(A, B, OP(C, D), OP(E, OP(F))) => OP(A, B, C, D, E, F)
unpack OP nil nil.
unpack OP ((app OP (tuple A))::AT) B :-
  !,
  unpack OP A BH,
  unpack OP AT BT,
  append BH BT B.
unpack OP (AH::AT) (AH::BT) :-
  unpack OP AT BT.


% may want something like... lists equal in any order,
% which sets up subgoals to go through the lists, comparing...
% (should be a method, i guess)

prettify_list _OP nil (str "").

prettify_list OP (A :: B)
  (blo 1 [OP, AA, BB]) :-
  !, prettify_term A AA, prettify_list OP B BB.

% an expression is "constant" if it has no headvars
% (ie nothing which is an abstraction)
% ...hmmm...don't understand this headvar stuff... now we write a term
% to a string to see if it is abstract

% NB: right now, (app (abs X\ X) r_one) will NOT be constant.

const_expr A :- not (has_subterm A), !, not(headvar_osyn A),
  term_to_string A AS, !, BS is (substring AS 0 4), not (BS = "<lc-").
const_expr (app A B) :- !, const_expr A, const_expr B.
const_expr (tuple (H::T)) :- !, const_expr H, const_expr (tuple T).
const_expr (tuple []) :- !.
const_expr (abs X) :- !, pi u\ (const_expr (X u)).
%const_expr (abs X\ Z) :- !.

has_subterm (app A B) :- !.
has_subterm (tuple A) :- !.
has_subterm (abs X) :- !.

not_equal A A :- !, fail.
not_equal (app A B) (app C D) :- !, not_equal A C ; not_equal B D.
not_equal (tuple (H1::T1)) (tuple (H2::T2)) :- !,
  not_equal H1 H2 ; not_equal (tuple T1) (tuple T2).
not_equal (tuple []) (tuple (H1::T1)) :- !.
not_equal (tuple (H1::T1)) (tuple []) :- !.
not_equal (abs X) (abs Y) :- !, pi u\ (not_equal (X u) (Y u)).
% if none of the above match, assume they are different
not_equal A B.

% matches if two terms are equal in the real sense
% (but might miss some; hopefully not after general rewrites, but
% probably so some)
r_equal A A.
r_equal (app plus (tuple A)) (app plus (tuple B)) :-
  is_permut A B.
r_equal (app times (tuple A)) (app times (tuple B)) :-
  is_permut A B.
r_equal (app div_by (tuple [N1, D1])) (app div_by (tuple [N2, D2])) :-
  r_equal N1 N2, r_equal D1 D2.

/*
subterm_of X Y Z :-
        not (not (Z = nil)),
        not (not (Z = [1])), !,
        subterm_of_ X Y Pos,
        reverse Pos Z.
subterm_of X Y Z :-
        reverse Z Pos,
        subterm_of_ X Y Pos.
subterm_of_ X _ _:- headvar_osyn X, !, fail.
subterm_of_ T T [].
subterm_of_ (app X _) Y (1::Pos) :- subterm_of_ X Y Pos.
subterm_of_ (app _ Y) X (2::Pos) :- subterm_of_ Y X Pos.
subterm_of_ (tuple X) T (N::Pos) :- nth X N Y _,
                                   subterm_of_ Y T Pos.
subterm_of_ (abs X) T Pos :- pi u\ (subterm_of_ (X u) T Pos).
*/

%
% ------------------ BASIC NUMS ------------------------ 
%

reals_list nil.
reals_list (reals :: A) :- reals_list A.

has_otype real_arith r_zero reals.
prettify_special r_zero (str "0") :- !.

has_otype real_arith r_one reals.
prettify_special r_one (str "1") :- !.

has_otype real_arith undefined reals.

has_otype real_arith plus ((tuple_type RL) arrow reals) :-
	  reals_list RL.


% nonzero, if the term _cannot_ be zero  %@todo, split up condition
nonzero A :- not(obj_atom A, A = r_zero).

% notzero, if the term is anything but r_zero
notzero r_zero :- !, fail.
notzero A.

% (rough method) to determine if sth is an integer
% may miss some cases, but will not say yes unless it is.
r_is_integer r_zero.
r_is_integer r_one.
r_is_integer neg_one.
r_is_integer (tuple (H::T)) :-
  r_is_integer H, r_is_integer (tuple T).
r_is_integer (tuple nil).
r_is_integer (app plus A) :- r_is_integer A.
r_is_integer (app times A) :- r_is_integer A.
r_is_integer (app minus A) :- r_is_integer A.

%
% --------------------- PLUS -------------------------- 
%

% plus(A) => A
definition real_arith plus_single trueP
  (app plus (tuple (A :: nil)))
  A.

% A+0 = A
definition real_arith plus_id trueP
  (app plus (tuple A))
  RES :-
     list_contains A r_zero,
     remove_all r_zero A NEW_A,
     make_plus_obj NEW_A RES.

make_plus_obj NEW_A (app plus (tuple NEW_A)) :- length NEW_A L, L > 1.
make_plus_obj (N1::nil) N1.
make_plus_obj nil r_zero.

% A+(B+C) = A+B+C
definition real_arith plus_plus trueP
  (app plus (tuple A))
  (app plus (tuple B)) :-
    list_contains A (app plus _C),
    unpack plus A B.

prettify_special (app plus (tuple [r_one, r_one]))
  (blo 1 [str "2"]).
prettify_special (app plus (tuple [r_one, r_one, r_one]))
  (blo 1 [str "3"]).
prettify_special (app plus (tuple [r_one, r_one, r_one, r_one]))
  (blo 1 [str "4"]).
prettify_special (app plus (tuple [r_one, r_one, r_one, r_one, r_one]))
  (blo 1 [str "5"]).

/*
prettify_special (app plus (tuple (r_one :: B)))
  (blo 1 [str "(", str FIRSTFIRST, RESTREST, str ")"]):-
  !, prettify_integers 1 B FIRST REST,
  !, prettify_int FIRST FIRSTFIRST, prettify_list (str "+") REST RESTREST.
*/

prettify_special (app plus (tuple (A :: B)))
  (blo 1 [str "(", AA, BB, str ")"]):-
  !, prettify_term A AA, prettify_list (str "+") B BB.

/*
prettify_int 0 "0".
prettify_int 1 "1".
prettify_int 2 "2".
prettify_int 3 "3".
prettify_int 4 "4".
prettify_int 5 "5".
prettify_int 6 "6".
prettify_int 7 "7".
prettify_int 8 "8".
prettify_int 9 "9".
prettify_int A S :-
  A>=10,
  AA=A/10,
  AB=A%10,
  prettify_int AA S1,
  prettify_int AB S2,
  S=S1+S2.

prettify_integers A nil A nil.
prettify_integers A (r_one :: B) RES REM :-
  !, AA = eval A+1,
  pretty_integeral AA B RES REM.
prettify_integers A (H::T) A (H::T) :- not (H = r_one).
*/


%
% ------------------- TIMES -------------------------- 
%

has_otype real_arith times ((tuple_type RL) arrow reals) :-
	  reals_list RL.

% A*1 = A
definition real_arith times_id trueP
  (app times (tuple A))
  RES :-
     remove_all r_one A NEW_A,
     make_times_obj NEW_A RES.

% list of factors in first term, osyn in second
make_times_obj NEW_A (app times (tuple NEW_A)) :- length NEW_A L, L > 1.
make_times_obj (N1::nil) N1.
make_times_obj nil r_one.

% A*0 = 0
definition real_arith times_zero trueP
  (app times (tuple A))
  r_zero :-
  list_contains A r_zero.

% puts any constant multiplier first
definition real_arith times_const trueP
  (app times (tuple T1))
  (app times (tuple T2)) :-
  move_const_expr_to_front T1 T2.

move_const_expr_to_front (H1::T1) (H1::T4) :-
  const_expr H1, !,
  move_const_expr_to_front T1 T4.

% crashes if we call T4 T3.. so we call it T4.
move_const_expr_to_front (H1::T1) (H2::T4) :-
  list_contains T1 H2,
  const_expr H2, !,
  remove H2 T1 T2,
  move_const_expr_to_front_2 (H1::T2) T4.

% will always succeed
move_const_expr_to_front_2 L1 L2 :-
  move_const_expr_to_front L1 L2, !.

move_const_expr_to_front_2 L1 L1.


% times(A) = A
definition real_arith times_single trueP
  (app times (tuple (A :: nil)))
  A.

% A*(B*C) = A*B*C
definition real_arith times_times trueP
  (app times (tuple A))
  (app times (tuple B)) :-
    list_contains A (app times _C),
    unpack times A B.

prettify_special (app times (tuple (A :: B)))
  (blo 1 [str "(", AA, BB, str ")"]):-
  !, prettify_term A AA, prettify_list (str "*") B BB.

% multiply out everything in a product
% only do so if the distributed term is non-const
definition real_arith dist_times_plus trueP
  (app times (tuple FS))
  (app plus (tuple (SF))) :-
  nth FS Pos (app plus (tuple F)) Rest,
  not ( const_expr (tuple F) ),
  factor_through_at F Rest Pos SF.

% factor_through_at Summends List Pos Result
% inserts each of the summends at pos'n Pos in List,
% applying times to each result, and returning a list...
% eg (a+b)*c*d => [a,b] [c,d] 1
% (semantics may be confusing... look carefully)
% 0 means apply at end
factor_through_at (SH::ST) Lf 0 ((app times (tuple RH))::RT) :- !,
  append Lf (SH::nil) RH,
  factor_through_at ST Lf 0 RT, !.
factor_through_at (SH::ST) Lf Pn ((app times (tuple RH))::RT) :-
  nth RH Pn SH Lf,
  factor_through_at ST Lf Pn RT, !.
factor_through_at nil _Lf _Pn nil :- !.

/*  //old dist routines, no longer used

definition real_arith dist_times_plus_1 trueP
  (app times (tuple [A, (app plus (tuple LIST))]))
  (app plus (tuple NEW_LIST)) :-
     factor_through A LIST NEW_LIST.

%  (app plus (tuple [(app times (tuple [A, B])), 
%                      (app times (tuple [A, C]))])).

definition real_arith dist_times_plus_2 trueP
  (app times (tuple [(app plus (tuple LIST)), A]))
  (app plus (tuple NEW_LIST)) :-
%  [(app times (tuple [B, A])), 
%                      (app times (tuple [C, A]))])) :-
  factor_through_right A LIST NEW_LIST.

% always multiply out constants
definition real_arith dist_times_plus_1_const trueP
  (app times (tuple [A, (app plus (tuple LIST))]))
  B :- 
  const_expr A,
  definition real_arith dist_times_plus_1 trueP
    (app times (tuple [A, (app plus (tuple LIST))]))
    B.

% always multiply out constants
definition real_arith dist_times_plus_2_const trueP
  (app times (tuple [(app plus (tuple LIST)), A]))
  B :-
  const_expr A, 
  definition real_arith dist_times_plus_2 trueP
    (app times (tuple [(app plus (tuple LIST)), A]))
    B.

factor_through A nil nil.
factor_through A (H :: T) 
  ( (app times (tuple [A, H])) ::
    NEW_T ) :- factor_through A T NEW_T.
factor_through_right A nil nil.
factor_through_right A (H :: T) 
  ( (app times (tuple [H, A])) ::
    NEW_T ) :- factor_through_right A T NEW_T.

*/

% collect terms

% writes a*b + a*c = (b+c)*a
% NOTE:  doesn't preserve order
% NOTE 2:  may be many ways sth can factor,
% eg x*y + 2*x +2*y + 1 = 2*(x+y)+x*y+1
% OR  = x*(y+2)+2*y+1 ...
% THOUGH what we'd like is (x+1)*(y+1)

definition real_arith collect_plus_times trueP
  (app plus (tuple SUM1))
  SUM5 :-
  remove (app times (tuple PR1)) SUM1 SUM2,
  remove (app times (tuple PR2)) SUM2 SUM3,
  remove F1 PR1 P11,
%  not (const_expr F1),
  remove F1 PR2 P21, 
!,
  make_times_obj P11 P12,
  make_times_obj P21 P22,
  append ((app times (tuple [(app plus (tuple [P12, P22])), F1]))::nil) SUM3 SUM4,
  make_plus_obj SUM4 SUM5, 
  !.

% this one collects any terms whose non-const parts match
% eg 3*x*y+y+2*x*y = 5*x*y

definition real_arith collect_obvious_factors trueP
    (app plus (tuple SUM1))
    SUM5 :-
  remove T1 SUM1 SUM2,
  not (const_expr T1),
  separate_const_terms T1 C1 V1,

  remove T2 SUM2 SUM3,
  separate_const_terms T2 C2 V2,
  r_equal (tuple V1) (tuple V2),   % likely to be very slow...
  
  make_times_obj C1 C1F,
  make_times_obj C2 C2F,
  make_times_obj V1 VF,
  append (app times (tuple [app plus (tuple [C1F, C2F]), VF])::nil) SUM3 SUM4,
  make_plus_obj SUM4 SUM5.

separate_const_terms (app times (tuple L)) C V :- !,
  separate_const_terms (tuple L) C V.
separate_const_terms (tuple (FH::FT)) (FH::CT) VT :-
  const_expr FH, !,
  separate_const_terms (tuple FT) CT VT.
separate_const_terms (tuple (FH::FT)) CT (FH::VT) :-
  not ( const_expr FH ), !,
  separate_const_terms (tuple FT) CT VT.
separate_const_terms (tuple nil) nil nil :- !.
% may insert a 1/1 in the vars list
separate_const_terms (app div_by (tuple [N, D])) 
    ((app div_by (tuple [r_one, DC]))::NCF)
    ((app div_by (tuple [r_one, DV]))::NVF) :- !,
  separate_const_terms N NCF NVF,
  separate_const_terms D DCF DVF,
%  make_times_obj NCF NC,
%  make_times_obj NVF NV,
  make_times_obj DCF DC,
  make_times_obj DVF DV.
separate_const_terms A (A::nil) nil :-
  const_expr A, !.
% last resort, assume it's a var
separate_const_terms A nil (A::nil) :- !.


%
% ------------------ NEG / MINUS -------------------------- 
%

has_otype real_arith neg (reals arrow reals).

has_otype real_arith neg_one reals.

known_additive_inverses r_one neg_one.
known_additive_inverses neg_one r_one.
known_additive_inverses A (app neg A).
known_additive_inverses (app neg A) A.
known_additive_inverses (app times (tuple [neg_one, A])) A.
known_additive_inverses A (app times (tuple [neg_one, A])).
known_additive_inverses (app times (tuple L1)) (app times (tuple L2)) :-
  remove neg_one L1 L1B,
  is_permut L1B L2.
known_additive_inverses (app times (tuple L2)) (app times (tuple L1)) :-
  remove neg_one L1 L1B,
  is_permut L1B L2.

definition real_arith neg_x trueP
  (app neg A)
  (app times (tuple [neg_one, A])) :-
  not ( A = (app plus (tuple _Sum)) ).

definition real_arith plus_additive_inverses trueP
  (app plus (tuple A))
  C2 :-
    remove T1 A B,
    remove T2 B C,
    known_additive_inverses T1 T2,
    make_plus_obj C C2.

definition real_arith times_neg_neg trueP
  (app times (tuple A))
  C2 :-
    remove neg_one A B,
    remove neg_one B C,
    make_times_obj C C2.

% could be eval'd by def of neg and expand,
% but this is more efficient
definition real_arith neg_sum trueP
  (app neg (app plus (tuple A)))
  (app plus (tuple NEW_A)) :-
  factor_through_at A (neg_one::nil) 0 NEW_A.


has_otype real_arith minus ((tuple_type [reals, reals]) arrow reals).

% a-b = a+(-1)*b ...
definition real_arith minus_to_plus_neg trueP
  (app minus (tuple [A, B]))
  (app plus (tuple [A, (app neg B)])).

prettify_special neg_one (str "-1").

prettify_special (app neg A)
  (blo 1 [str "-(", AA, str ")"]):-
  !, prettify_term A AA.

prettify_special (app minus (tuple [A, B]))
  (blo 1 [str "(", AA, str "-(", BB, str "))"]):-
  !, prettify_term A AA, prettify_term B BB.


%
% -------------------- DIV_BY -------------------------- 
%

has_otype real_arith div_by ((tuple_type [reals, reals]) arrow reals).

% A/1 = A
definition real_arith div_by_one trueP
  (app div_by (tuple [A, r_one]))
  A.

% 0/D = 0
definition real_arith div_zero_by trueP
  (app div_by (tuple [r_zero, D]))
  r_zero :- nonzero D.

% A/-1 = -A
definition real_arith div_by_neg_one trueP
  (app div_by (tuple [A, neg_one]))
  (app neg A).

% A/(-1*B) = (-1*A)/B
definition real_arith div_by_neg_one_factor trueP
  (app div_by (tuple [N, (app times (tuple D))]))
  (app div_by (tuple [(app times (tuple [neg_one, N])), 
			(app times (tuple D2))])) :-
    remove neg_one D D2.

% A*(B/C) = (A*B)/C
definition real_arith times_div_by trueP
  (app times (tuple FACTORS))
  (app div_by (tuple [
      (app times (tuple NEW_FACTORS)), FD])) :-
    list_contains FACTORS (app div_by (tuple [FN, FD])),
    remove (app div_by (tuple [FN, FD])) FACTORS NEW_FACTORS_1,
    append NEW_FACTORS_1 (FN::nil) NEW_FACTORS. 

% (A/B)/C = A/(B*C)
definition real_arith div_div_by trueP
  (app div_by (tuple [(app div_by (tuple [NN, ND])), D]))
  (app div_by (tuple [NN, (app times (tuple [ND, D]))])).

% A/(B/C) = (A*C)/B
definition real_arith div_by_div_by trueP
  (app div_by (tuple [N, (app div_by (tuple [DN, DD]))]))
  (app div_by (tuple [(app times (tuple [N, DD])), DN])).

definition real_arith div_x_by_x_1 trueP
  (app div_by (tuple [A, A]))
  r_one.

definition real_arith div_x_by_x_2 trueP
  (app div_by (tuple [(app times (tuple N1)), (app times (tuple D1))]))
  (app div_by (tuple [(app times (tuple N2)), (app times (tuple D2))])) :-
    list_contains N1 X, list_contains D1 X,
    remove X N1 N2, remove X D1 D2.

definition real_arith div_x_by_x_3 trueP
  (app div_by (tuple [(app times (tuple N1)), D1]))
  (app times (tuple N2)) :-
    remove D1 N1 N2.

definition real_arith div_x_by_x_4 trueP
  (app div_by (tuple [N1, (app times (tuple D1))]))
  (app div_by (tuple [r_one, (app times (tuple D2))])) :-
    remove N1 D1 D2.

% a + b/c = (ac+b)/c
definition real_arith plus_div_by trueP
  (app plus (tuple ADDENDS))
  (app div_by (tuple [(app plus (tuple N)), D])) :-
    nth ADDENDS PN (app div_by (tuple [N1, D])) LEFTOVER,
    factor_through_at LEFTOVER (D::nil) 1 N_LEFTOVER,
    append N_LEFTOVER (N1::nil) N.

prettify_special (app div_by (tuple [A, B]))
  (blo 1 [str "(", AA, str "/", BB, str ")"]):-
  !, prettify_term A AA, prettify_term B BB.


%
% --------------------- MISC ------------------------- 
%


%definition real_arith beta_redux_1 trueP
%  (abs X\ (app A X))
%  A.

% equal to "beta_reduction" defined in constructive_logic...
%definition real_arith beta_redux_2 trueP
%  (app (abs X\ (app A X)) Y)
%  (app A Y).

definition real_arith beta_redux trueP
  (app (abs Z\ U Z) X)
  (U X).

%definition real_arith beta_redux_plus trueP
%  (app (abs Z\ (app plus (tuple [(app A Z), (app B Z)])) ) X)
%  (app plus (tuple [(app A X), (app B X)]))
%  .

% these next don't really do anything

has_otype real_arith fn_idty (reals arrow reals).
has_otype real_arith fn_indep (reals arrow reals).

definition real_arith def_fn_idty trueP
  (app fn_idty X)
  X.

% fn f is indep if f(_)=f(0)
definition real_arith def_fn_indep trueP
  (app fn_indep _)
  (app fn_indep r_zero).


%
% ---------------- ALGEBRA METHODS ------------------------ 
%

% method to check A=B by writing A-B=0

atomic real_arith rearrange_set_equal_zero
        ( seqGoal (H >>> (app eq (tuple [A, B]))  ) )
	( nonzero A, nonzero B )
        true
        (seqGoal (H >>> (app eq (tuple [(app minus (tuple [A, B])), r_zero]))) )
        notacticyet.



%
% ---------------- SUMMARY METHODS ------------------------ 
%

compound real_arith tauts_meth (repeat_meth
            (orelse_meth trivial
            (orelse_meth false_e
            (orelse_meth neg_i
            (orelse_meth neg_e
            (orelse_meth imp_i
            (orelse_meth all_i  
            (orelse_meth exists_i 
            (orelse_meth and_i
            (orelse_meth and_e
            (orelse_meth imp_e1
            (orelse_meth imp_e2
            (orelse_meth imp_e3
            (orelse_meth imp_e3
            (orelse_meth or_il 
              or_ir
  )))))))))))))))
  _
  true.

compound real_arith arith_top_meth (complete_meth
    (real_arith_methods arith_general_methods)
  )
  _
  true.

%whatever the "NextMeth" is must succeed...
%hack to speed things up; wrap in try_meth if it's not guaranteed...
compound real_arith (real_arith_methods NextMeth)
    (then_meth (try_meth NextMeth)
    (then_meth (try_meth (expand_then_collect NextMeth))
    (then_meth (try_meth (combine_fracs NextMeth))
    trivial
  )))
  _
  true.

%
% method should be:  ALL (trivial, taut, rewrites, trivial); 
% expand_distribution, ALL ;
% collect_terms ALL ; 
% combine_fracs, (above) ;
% pow as exp, (above) ;
% exp log as pow (above but last)

% all "general_methods" must succeed, if they are passed as nextMeth
% hack to speed things up b/c cut_meth not implemented
compound real_arith arith_general_methods
    (then_meth (try_meth (trivial))
    (then_meth (try_meth tauts_meth)
    (then_meth (try_apply_rewrites general_rewrites)
       (try_meth (trivial))
  )))
  _
  true.

compound real_arith (expand_then_collect NextMeth)
    (then_meth 
         (then_meth (apply_rewrites expand_rewrites)
            NextMeth)
    (then_meth 
         (try_meth (then_meth rearrange_set_equal_zero
           NextMeth))
    (then_meth 
         (collect_terms NextMeth)
    (try_meth trivial))))
    _ true.

% @todo
compound real_arith (collect_terms NextMeth)
    (then_meth 
         (try_meth (then_meth (apply_rewrites collect_rewrites)
            NextMeth))
    (try_meth (trivial)))
    _ true.

% @todo
compound real_arith (combine_fracs NextMeth)
    (then_meth 
         (then_meth (apply_rewrites combine_fracs_rewrites)
            (then_meth NextMeth
              (expand_then_collect NextMeth)))
    (try_meth trivial))
    _ true.

% do all rewrites in r_one fell swoop

rewrites_set lxtest Set nil.
rewrites_set Theory Set nil :- 
  fail.
% might want to have nil set as a default
% (problem is, it is taking priority!)
/*
  rewrites_set_nil Theory Set _List.

rewrites_set_nil T Set List :-
  rewrites_set T Set List,
  printstdout "got list",
  printstdout List,
  list_contains List A,
  !,
  fail.
*/
rewrites_set_nil _Theory _Set nil.

clear_rewrites_set Predicate Loop :-
  ((rewrites_set lxtest Predicate nil :- !) => (Loop)).

with_rewrites_set Predicate RW Loop :- 
     rewrites_set _T1 Predicate RW1, !,
     append RW1 RW RW2,
     ((rewrites_set _T2 Predicate RW2 :- !) => (Loop)).

with_theory_rewrites_set Theory Predicate Loop :-
     rewrites_set lxtest Predicate RW1, 
     rewrites_set Theory Predicate RW, !,
     append RW1 RW RW2,
     ((rewrites_set lxtest Predicate RW2 :- !) => (Loop)).

compound real_arith (apply_rewrites ListPredicate)
  (apply_rewrites_record ListPredicate _ApplicationList _G1 _G2)
  _
  true.

atomic real_arith (apply_rewrites_record ListPredicate ApplicationList G G1)
        ( seqGoal (H >>> G))
	(rewrites_set _Theory ListPredicate RuleList, !,
         do_apply_rewrites_1 RuleList ApplicationList H G G1)
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

% as above, but guaranteed to succeed
% (speeds things up since we don't have cutmeth)
compound real_arith (try_apply_rewrites ListPredicate)
  (try_apply_rewrites_record ListPredicate _ApplicationList _G1 _G2)
  _
  true.

atomic real_arith (try_apply_rewrites_record ListPredicate ApplicationList G G1)
        ( seqGoal (H >>> G))
	(rewrites_set _Theory ListPredicate RuleList, !,
         do_apply_rewrites_2 RuleList ApplicationList H G G1)
        true 
        (seqGoal (H >>> G1))
        notacticyet :- !.

do_apply_rewrites_1 RuleList (Rule::ApplicationList) H G GF :-
         rewrite_with_rules RuleList Rule G G1 Cond,
         trivial_condition Cond H,
            % check the condition is in the hypotheses
	 !,
	 print "Rewriting (everything) with ",
	 pprint_name Rule,
         print "New goal: ",
         pprint_term G1,
	 !,
	 do_apply_rewrites_2 RuleList ApplicationList H G1 GF.

do_apply_rewrites_2 RuleList ApplicationList H G GF :-
	 do_apply_rewrites_1 RuleList ApplicationList H G GF, !.
do_apply_rewrites_2 RuleList nil H G G :- !,
         print "Done rewriting (everything).\n".




%
% -------------------- QUERIES ------------------------ 
% 

top_goal real_arith test_plus_1 []
	  (app eq (tuple [
	    (app plus (tuple [r_one])),
	    r_one
	    ])).

top_goal real_arith test_plus_2 []
	  (app forall (tuple [reals, (abs X\ 
             (app eq (tuple [
                 (app plus (tuple [(app plus (tuple [r_zero, X])),
 	            r_zero, r_zero])),
		 X])))])).

top_goal real_arith test_redux_1 []
  (app forall (tuple [reals, (abs X1\
    (app eq (tuple [
       (app times (tuple [(app (abs X2\ r_one) X1), X1])),
       (app (abs X2\ X2) X1)] ))
  )])).


top_goal real_arith test_redux_2 []
  (app forall (tuple [reals, (abs X\
    (app eq (tuple [
       (app (abs Z\ (app plus (tuple [(app neg Z), (app neg Z)]))) X),
       (app times (tuple [(app plus (tuple [r_one, (app (abs Z\ r_one) X)])),
          (app neg X)])) 
    ]))
  )])).

top_goal real_arith test_times_1 []
	  (app forall (tuple [reals, (abs X\ 
             (app eq (tuple [
                 (app times (tuple [(app times (tuple [r_one, X])), r_one])),
		 X])))])).

top_goal real_arith test_times_2 []
	  (app forall (tuple [reals, (abs X\ 
             (app eq (tuple [
                 (app times (tuple [(app times (tuple [r_zero, X])), r_one])),
		 r_zero])))])).

top_goal real_arith test_times_3 []
	  (app forall (tuple [reals, (abs X\ 
             (app eq (tuple [
                 (app times (tuple [
                   (app plus (tuple [r_one, r_one])),
                   (app plus (tuple [r_one, r_one])),
                   (app plus (tuple [r_one, r_one])) ])),
                 (app plus (tuple [r_one, r_one, r_one, r_one,
		   r_one, r_one, r_one, r_one]))
             ])))])).

top_goal real_arith test_times_plus_1 []
	  (app forall (tuple [reals, (abs X\ 
             (app eq (tuple [
                 (app times (tuple [(app plus (tuple [r_zero, r_one])), X])),
		 X])))])).


top_goal real_arith test_dist_1 []
	  (app forall (tuple [reals, (abs X\ 
  	    (app forall (tuple [reals, (abs Y\ 
              (app eq (tuple [
                 (app times (tuple [X, 
                    (app plus (tuple [r_one, X]))])),
                 (app times (tuple [ 
                    (app plus (tuple [r_one, X])), X]))
		])))])))])).

top_goal real_arith test_plus_neg_1 []
  (app eq (tuple [
    (app plus (tuple [r_one, neg_one])), r_zero ])).
  
top_goal real_arith test_minus_1 []
	  (app forall (tuple [reals, (abs X\ 
  	    (app forall (tuple [reals, (abs Y\ 
              (app eq (tuple [
                 (app minus (tuple [X, 
                    (app plus (tuple [(app neg r_zero), X, (app neg Y)]))])),
                 Y
		])))])))])).


top_goal real_arith test_div_by_1 []
	  (app forall (tuple [reals, (abs X\ 
  	    (app forall (tuple [reals, (abs Y\ 
              (app eq (tuple [
	         (app times (tuple [neg_one,
                   (app div_by (tuple [(app neg X), 
                    (app times (tuple [(app neg Y), X, neg_one]))]))])),
                 (app div_by (tuple [r_one, Y]))
		])))])))])).


top_goal real_arith test_fail_plus []
	  (app eq (tuple [
	    (app plus (tuple [r_one, r_one])),
	    (app plus (tuple [r_one, r_zero]))
	    ])).


top_goal real_arith test_fail_dist []
  (app forall (tuple [reals, (abs X\ 
	  (app eq (tuple [
	    (app times (tuple [X, (app plus (tuple [r_one, r_one]))])),
	    (app minus (tuple [X, r_zero]))
	    ]))
	)])).


% using only the constants reduction rules...(which we no longer do)
% don't reduce...x*(1+1)*y = x*1*y+x*1*y  _2
% do resuce (1+1)*(1+1) = 1+1+1+1
% do reduce (1+1)*(x+x)*(y+y) = (1+1)*x*(y+y) + (1+1)*x*(y+y)
% a*(b+c)*d = a*b*d + a*c*d  if  a  is const_expr with plus

top_goal real_arith test_dist_const_1 []
	  (app forall (tuple [reals, (abs X\ 
              (app eq (tuple [
	         (app times (tuple [
                   (app plus (tuple [X, X])),
                   (app plus (tuple [r_one, r_one])) ])),
	         (app plus (tuple [
                   (app times (tuple [X,
                     (app plus (tuple [r_one, r_one])) ])),
                   (app times (tuple [X,
                     (app plus (tuple [r_one, r_one])) ])) ]))
              ])) )])).

top_goal real_arith test_dist_const_3 []
	  (app forall (tuple [reals, (abs X\ 
              (app eq (tuple [
	         (app times (tuple [
                   (app plus (tuple [X, X])),
                   (app plus (tuple [r_one, r_one])) ])),
	         (app times (tuple [X,
                   (app plus (tuple [r_one, r_one, r_one, r_one])) ]))
              ])) )])).

top_goal real_arith test_dist_const_2 []
	  (app forall (tuple [reals, (abs X\ 
              (app eq (tuple [
	         (app times (tuple [
                   (app plus (tuple [X])),
                   (app plus (tuple [r_one, r_one])) ])),
	         (app plus (tuple [X, X]))
              ])) )])).

top_goal real_arith test_add_fracs_1 []
  (app eq (tuple [
    (app plus (tuple [ r_one, (app div_by 
       (tuple [r_one, (app plus (tuple [r_one, r_one]))])) ])),
    (app div_by (tuple [ (app plus (tuple [r_one, r_one, r_one ])), 
       (app plus (tuple [r_one, r_one])) ]))
  ])).

% this test should succeed with only [idty, dist_times_plus]
% as the rewrites
top_goal real_arith test_dist_times_plus_1 []
(app forall (tuple [reals, (abs X\
(app forall (tuple [reals, (abs Y\
  (app eq (tuple [
     (app times (tuple [X, Y,
        (app plus (tuple [X, Y])) ])),
     (app plus (tuple [
        (app times (tuple [X, Y, X])),
        (app times (tuple [X, Y, Y])) ]))
  ])) )])) )])).
do_test_dist_times_plus_1 :-
  with_clear_arith_rewrites
    (with_rewrites_set general_rewrites [idty, dist_times_plus]
    (pds_plan arith_top_meth test_dist_times_plus_1
  )).
% but should fail w/ everything _but_ dist_times_plus.
do_test_dist_times_plus_fail_1 :-
  rewrites_set real_arith general_rewrites RW1,
  rewrites_set real_arith expand_rewrites RW2,
  append RW1 RW2 RW3,
  remove dist_times_plus RW3 RW4,
  with_clear_arith_rewrites
    (with_rewrites_set general_rewrites RW4
    (pds_plan arith_top_meth test_dist_times_plus_1
  )).
  
do_test_remove_all_1 :-
  remove_all r_one (r_one::r_zero::r_one::nil) (r_zero::nil).

do_test_remove_all_fail_1 :-
  remove_all r_one (r_one::r_zero::r_one::nil) nil.

top_goal real_arith test_collect_1 []
  (app eq (tuple [
     (app plus (tuple [r_zero, r_one,
        (app times (tuple [r_zero, r_one])), 
        (app times (tuple [r_one, r_one])) 
     ])),
     (app plus (tuple [
        (app times (tuple [
           (app plus (tuple [r_zero, r_one])), r_one])),
        r_zero, r_one]))
  ])).
top_goal real_arith test_fail_collect_1 []
  (app eq (tuple [
     (app plus (tuple [r_zero, r_one,
        (app times (tuple [r_zero, r_one])), 
        (app times (tuple [r_one, r_one]))
     ])),
     (app plus (tuple [
        (app times (tuple [
           (app plus (tuple [r_one, r_one])), r_one])),
        r_zero, r_one]))
  ])).
do_test_collect_1 :-
  rewrites_set real_arith collect_rewrites RW1,
  append RW1 [idty] RW2,
  with_clear_arith_rewrites
    (with_rewrites_set general_rewrites RW2
    (pds_plan arith_top_meth test_collect_1)
  ).
do_test_fail_collect_1 :-
  rewrites_set real_arith collect_rewrites RW1,
  append RW1 [idty] RW2,
  with_clear_arith_rewrites
    (with_rewrites_set general_rewrites RW2
    (pds_plan arith_top_meth test_fail_collect_1)
  ).

%
% --------------- SUMMARY / SETUP / TEST ------------------------ 
%

do_real_arith_tests :-
  test_set real_arith_tests T,
  test_set real_arith_anti_tests AT,
  test_set real_arith_queries Q,
  test_set real_arith_anti_queries AQ,
  do_test_battery "real_arith" T AT
    with_setup_real_arith arith_top_meth Q AQ.

clear_arith_rewrites :- with_clear_arith_rewrites (testloop nop).
with_clear_arith_rewrites Loop :-
  (clear_rewrites_set general_rewrites
  (clear_rewrites_set expand_rewrites
  (clear_rewrites_set collect_rewrites
  (clear_rewrites_set combine_fracs_rewrites
  (Loop))))).

setup_real_arith :- with_setup_real_arith (testloop nop).
with_setup_real_arith Loop :- 
  (with_theory_rewrites_set real_arith general_rewrites
  (with_theory_rewrites_set real_arith expand_rewrites
  (with_theory_rewrites_set real_arith collect_rewrites
  (with_theory_rewrites_set real_arith combine_fracs_rewrites
  (Loop))))).

% list of commands which must pass
test_set real_arith_tests (
     do_test_dist_times_plus_1 :: 
     do_test_remove_all_1 ::
     do_test_collect_1 ::
  nil).

% list of commands which MUST NOT PASS
test_set real_arith_anti_tests (
     do_test_dist_times_plus_fail_1 ::
     do_test_remove_all_fail_1 ::
     do_test_fail_collect_1 ::
  nil).

% list of tests which must pass in normal operation
test_set real_arith_queries 
  [
     test_plus_1, test_plus_2,
     test_redux_1, test_redux_2,
     test_times_1, test_times_2,
     test_times_plus_1, test_dist_1,
     test_collect_1,
     test_plus_neg_1, test_minus_1, test_div_by_1
  ].

% list of tests which MUST NOT PASS in normal operation
test_set real_arith_anti_queries [
     test_fail_plus, test_fail_dist
%,     test_fail_collect_1
  ].


% rewrites that are always good
rewrites_set real_arith general_rewrites [
     idty,
     beta_redux, 
     times_times, times_id, times_single, times_zero, times_const,
     div_zero_by, div_by_one, div_by_neg_one, div_by_neg_one_factor,
     times_div_by, div_div_by, div_by_div_by,
     div_x_by_x_1, div_x_by_x_2, div_x_by_x_3, div_x_by_x_4,
     plus_plus, plus_single, plus_id, 
     neg_x, plus_additive_inverses, neg_sum, times_neg_neg,
     minus_to_plus_neg,
     collect_obvious_factors
  ].

% rewrites which expand in potentially useful ways
rewrites_set real_arith expand_rewrites [
      dist_times_plus
  ].

% rewrites which simplify in potentially useful ways
rewrites_set real_arith collect_rewrites [
    collect_plus_times
  ].

rewrites_set real_arith combine_fracs_rewrites [
     plus_div_by
  ].

end
