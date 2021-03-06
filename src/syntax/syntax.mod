/*

File: syntax.mod
Author: Louise Dennis / James Brotherston
Description:  Support for lclam HOAS syntax.
Last Modified: 13th August 2002

*/

module syntax.

local dummysyn osyn.
local synmemb  (osyn -> osyn -> list (list osyn) -> o).
local replace_nout int -> int -> osyn -> osyn -> o.
local replace_with_abs osyn -> osyn -> (osyn -> osyn) -> osyn -> o.
local copy_term_ osyn -> osyn -> int -> int -> int -> int -> o.
local rec_copy_term_ (list osyn) -> (list osyn) -> int -> int -> int -> int -> o.
local subterm_of_ osyn -> osyn -> (list int) -> o.

local replace_at_ osyn -> osyn -> osyn -> (list int) -> o.
local pos_not_headvar_osyn_ (list int) -> o.

headvar_osyn Y:-
	not (not (Y = (user_object "dummy_syntax_dont_use_elsewhere"))).

%% Test to make sure that something is a syntax atom.     
obj_atom (app _ _) :- !, fail.
obj_atom (abs _ _) :- !, fail.
obj_atom (otype_of _ _) :- !, fail.
%% obj_atom (tuple _) :- !, fail.
obj_atom _.            

%
% copy_term
%
/*
copy_term X Y1:-
	rec_copy_term_ X Y 0 Nout 0 About, !,
	c_match X Y1, !,
	replace_nout Nout About Y Y1, 
	!.
*/

type z osyn.
type y osyn.

local collect_list osyn -> (list X) -> (list X) -> o.
local rec_collect_list (list osyn) -> (list X) -> (list X) -> o.
local change_var_names osyn -> (list (list osyn)) -> osyn -> o.
local rec_change_var_names (list osyn) -> (list (list osyn)) ->(list osyn) -> o.

%%%%%% COPY_TERM/2 

copy_term X Y :-
        rec_collect_list X [] List,
        rec_change_var_names X List Y.


%%%% SPECIAL MEMBER FUNCTION
%%%% succeed only if the first element of the tuple is the already unified
%%%% with the the first element of the tuple at the head of the list
%%%% if not then prevent unification using not (not ...).

synmemb A B [[X,B]|_] :- 
        not (A = z, X = y).

synmemb A B [[X,C]|T] :-
        not (not (A = z, X = y)),
        synmemb A B T.

%%%% CHANGE_VAR_NAMES
%%%% go through the term tree- when a variable is encountered look it up in the 
%%%% list and replace with the second element of the corresponding tuple
%%%% Not yet implemented for renaming abstraction variables.
        
change_var_names X _ X:-
        not (headvar_osyn X),
        obj_atom X.

change_var_names X List B :-
        headvar_osyn X,
        synmemb X B List.

change_var_names X _ X:-
        not (headvar_osyn X),
        X = (otype_of _ _).

change_var_names X List (app C D):-
        not (headvar_osyn X),
        X = (app A B),
        change_var_names A List C,
        rec_change_var_names B List D.

change_var_names X List (abs Y Type) :-
        not (headvar_osyn X),
        X = (abs A Type),
        pi u\ (change_var_names (A u) List (Y u)).

%%% recursive auxiliary function

rec_change_var_names nil List nil.

rec_change_var_names (H::T) List (H1::T1) :-
        change_var_names H List H1,
        rec_change_var_names T List T1.
        

%%%% COLLECT_LIST
%%%% go through term tree and add a tuple to the list when a var is encountered

collect_list X In In :-
        not (headvar_osyn X),
        obj_atom X.

collect_list X In [[X,_Tempvar]|In] :-
        headvar_osyn X, !.

collect_list Z In In :-
        Z = (otype_of _ _).

collect_list Z In Out :-
        Z = (app X Y),
        collect_list X In Mid,
        rec_collect_list Y Mid Out.

collect_list Z In Out :-
        Z = (abs A Type),
        pi u\ (collect_list (A u) In Out).

%%% recursive auxiliary function

rec_collect_list [] O O.

rec_collect_list (H::T) In Out:-
        collect_list H [] NewIn,
        append NewIn In Mid,
        rec_collect_list T Mid Out.

% Because of typing we need to distinguish between first and second order
% syntax terms using counting and counting_abs and keep track of how many
% of each we have used.
copy_term_ A (counting Nin) Nin Nout Ab Ab:-	
	(not (not (A = (counting Nin)))),
	!,
	Nout is (Nin + 1).
copy_term_ T T N N A A:- obj_atom T, !.
copy_term_ (app X Y) (app X1 Y) Nin Nout Abin About:- 
	copy_term_ X X1 Nin Nin1 Abin About1, 
	rec_copy_term_ Y Y1 Nin1 Nout About1 About, !.
copy_term_ (abs A Type) (abs (X\ (counting_abs Abin X)) Type) Nin Nin Abin About:-
	(not (not (A = (X\ (counting_abs Abin X))))),
	!,
	About is (Abin + 1).
copy_term_ (abs F Type) (abs F1 Type) Nin Nout Abin About:- pi u\ (copy_term_ (F u) (F1 u) Nin Nout Abin About), !.

rec_copy_term_ nil nil Nin Nin About About.
rec_copy_term_ (X::T) (X1::T1) Nin Nout Abin About:-  
	copy_term_ X X1 Nin Nin1 Abin About1, 
	rec_copy_term_ T T1 Nin1 Nout About1 About, !.

replace_nout 0 0 Y Y:- !.
replace_nout 0 0 _ _:- !, fail.
replace_nout 0 N Y Y1:-
	N1 is (N - 1), !,
	replace_with_abs Y (abs (X\ (counting_abs N1 X)) Type) A Y2,
	c_match Y2 Y1, !,
	replace_nout 0 N1 Y2 Y1, !.
replace_nout N AbsCount Y Y1:-
	N1 is (N - 1), !,
	replace_with Y (counting N1) A Y2,
	c_match Y2 Y1, !,
	replace_nout N1 AbsCount Y2 Y1, !.

local c_match osyn -> osyn -> o.
/*
c_match X Y:-
	printterm std_out X, print "\n",
	printterm std_out Y, print "\n", 
	fail.
*/
c_match X Y:- headvar_osyn Y, !.
c_match X X.
c_match X _:- not (headvar_osyn X), X = (counting _), !.
c_match X _:- (headvar_osyn X), !, fail.
c_match (abs (Y\ (counting_abs _ Y)) _) _.
c_match (app X Y) (app X1 Y1):- !,
	c_match X X1,
	mappred Y c_match Y1.
c_match (abs (X\ (F X)) TYpe) (abs (X1\ (G X1)) Type):- !,
	pi u\ (c_match (F u) (G u)).

%
% subterm_of
%

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
subterm_of_ (app _ Y) X (N1::Pos) :- nth Y N ST _,
				     subterm_of_ ST X Pos,
				     N1 is N + 1.
subterm_of_ (abs X _) T Pos :- pi u\ (subterm_of_ (X u) T Pos).

%
% replace_at_
%

% AH 2002/11/13 moved this test to separate predicate with cut;
% without it I was sometimes getting two equiv results
% (which made the proofs much longer!!)
% [not sure why this test is here anyways...]
pos_not_headvar_osyn_ Pos :-
  (not (Pos = nil) ; not (Pos = [1])), !.

replace_at A B C Pos:-
	pos_not_headvar_osyn_ Pos,
	reverse Pos P,
	replace_at_ A B C P.
replace_at_ _ T T [].
replace_at_ (app X Y) T (app X1 Y) (1::Pos) :- replace_at_ X T X1 Pos.
replace_at_ (app X Y) T (app X Y1) (N::Pos) :- (not (N = 1)),
	N1 is N - 1,
        nth Y N1 ST Rest,
        replace_at_ ST T NY Pos,
	nth Y1 N1 NY Rest.
replace_at_ (abs X Type) T (abs X1 Type) Pos :- pi u\ (replace_at_ (X u) T (X1 u) Pos).

replace_with In _ _ In:- headvar_osyn In, !.
replace_with In In Out Out:- !.
replace_with (counting_abs N A) In Out (counting_abs N AOut):-
	replace_with A In Out AOut, !.
replace_with (app X Y) In Out (app X1 Y1) :- replace_with X In Out X1,
					     mappred Y (A\ B\ replace_with A In Out B) Y1, !.
replace_with (abs F Type) In Out (abs F1 Type) :- pi u\ (replace_with (F u) In Out (F1 u)), !.
replace_with A _ _ A.

replace_with_abs In _ _ In:- headvar_osyn In, !.
replace_with_abs (counting_abs N Const) (abs (X\ counting_abs N X) Type) Out (Out Const).
replace_with_abs (app X Y) In Out (app X1 Y1) :- replace_with_abs X In Out X1,
			mappred Y (A\ B\ replace_with_abs A In Out B) Y1, !.
replace_with_abs (abs F Type) In Out (abs F1 Type) :- pi u\ (replace_with_abs (F u) In Out (F1 u)), !.
replace_with_abs A _ _ A.

has_otype_ Term Type:-
	headvar_osyn Term, !.
has_otype_ Term universe:-
	is_otype _ Term _ _.
has_otype_ A B:-
	has_otype _ A B.
has_otype_ A B:-
	   obj_atom A,
	   not (has_otype _ A _).
has_otype_ (app F T) B :-
  has_otype_ F (arrow A B),
  mappred T (X\ Y\ (has_otype_ X Y)) A.
has_otype_ (abs L Type) (arrow [Type] B):-
  pi x\ ((has_otype Z x Type) => (has_otype_ (L x) B)).
has_otype_ (abs L A) (arrow (A::T) B):-
  pi x\ ((has_otype Z x A) => (has_otype_ (L x) (arrow T B))).

/* env_otype A B C:-
	printstdout A,
	printstdout B,
	printstdout C,
	fail.
*/
env_otype Term Hyps Type:-
	not (headvar_osyn Term),
	has_otype _ Term Type, 
	!.
env_otype  Term Hyps Type:-
	not (headvar_osyn Term),
	not (headvar_osyn Type),
	not (member (hyp (otype_of Term _) _) Hyps),
	obj_atom Term, !,
	not (has_otype _ Term _).
env_otype  Term Hyps Type :- 
	not (headvar_osyn Term),
	member (hyp ( otype_of Term Type ) _) Hyps, !.
env_otype  Term Hyps Type:-
	not (headvar_osyn Term),
	member (hyp ( otype_of Term Type1 ) _) Hyps, !,
	not (Type1 = Type), fail.
env_otype  Term Hyps Type :- 
	not (headvar_osyn Term),
	member (hyp ( otype_of Term Type2 ) _) Hyps, not (Type = Type2), !, 
        fail.
env_otype  Term Hyps Type :- 
	not (headvar_osyn Term),
	obj_atom Term, !.
env_otype  Term _ Type :- headvar_osyn Term, !.
env_otype  (app F List) Hyps OT3 :-
            env_otype F Hyps (arrow ListTypes OT3),
            mappred List (X\ Y\ env_otype X Hyps Y) ListTypes, !.
env_otype (abs L A) Hyps (arrow [A] B):-
  pi x\ ((has_otype Z x A) => (env_otype (L x) Hyps B)).
env_otype (abs L A) Hyps (arrow (A::T) B):-
  pi x\ ((has_otype Z x A) => (env_otype (L x) Hyps (arrow T B))).


%% Not to be used with terms involving meta-variables.
%% env_otype_inst_types A B C:-
%%	printstdout A,
%%	printstdout B,
%%	printstdout C,
%%	fail.
env_otype_inst_types  Term Hyps Type:-
	has_otype _ Term Type, !.
env_otype_inst_types  Term Hyps Type:-
	member (hyp ( otype_of Term Type ) _) Hyps, !.
env_otype_inst_types  Term Hyps Type:-
	obj_atom Term,
	not (has_otype _ Term _), 
	member (hyp ( otype_of Term Type ) _) Hyps, !.
env_otype_inst_types  Term Hyps Type:-
	obj_atom Term,
	not (has_otype _ Term _), 
	member (hyp ( otype_of Term Type1 ) _) Hyps, !,
	not (Type1 = Type), fail.
env_otype_inst_types  Term Hyps Type:-
	obj_atom Term,
	not (has_otype _ Term _), !.
env_otype_inst_types  (app F List) Hyps OT3 :-
        env_otype_inst_types F Hyps (arrow ListTypes OT3),
        mappred List (X\ Y\ (env_otype_inst_types X Hyps Y)) ListTypes, !.
env_otype_inst_types (abs L A) Hyps (arrow [A] B):-
  pi x\ ((has_otype Z x A) => (env_otype_inst_types (L x) Hyps B)).
env_otype_inst_types (abs L A) Hyps (arrow (A::T) B):-
  pi x\ ((has_otype Z x A) => (env_otype_inst_types (L x) Hyps (arrow T B))).

%% Succeeds if Term is a constant (ie. contains no bound variables) of Type.
constant Term Type:-
	headvar_osyn Term, !.
constant Term universe:-
	is_otype _ Term _ _.
constant A B:-
	has_otype TH A B,
	not (TH = bound).
constant (app F T) B :-
  constant F (arrow A B),
  mappred T (X\ Y\ (constant X Y)) A.
constant (abs L A) (arrow [A] B):-
  pi x\ ((has_otype Z x A) => (constant (L x) B)).

%% Succeeds if Term contains a meta_variable.
contains_meta_var_term Term:-
		       headvar_osyn Term, !.
contains_meta_var_term (app Rator Rand):-
		  contains_meta_var_term Rator; 
                  for_one Rand contains_meta_var_term _.
contains_meta_var_term (abs Term _):-
		       pi x\ (contains_meta_var_term (Term x)).



end
