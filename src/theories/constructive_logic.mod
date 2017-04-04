/*

File: constructive_logic.mod
Author: Louise Dennis / James Brotherston
Description: Theory of logic with equality
Last Modified: 20th August 2002

*/

module constructive_logic.

local atomic_term    osyn -> o.
local impe_rule       meth -> osyn -> osyn -> osyn -> goal -> (list context) -> o.


/*
SYNTAX CONSTANTS
*/

is_otype constructive_logic bool [trueP, falseP] nil.

has_otype constructive_logic and (arrow [bool, bool] bool).
has_otype constructive_logic or (arrow [bool, bool] bool).
has_otype constructive_logic imp (arrow [bool, bool] bool).
has_otype constructive_logic neg (arrow [bool] bool).
has_otype constructive_logic forall (arrow [universe, (arrow [X] bool)] bool).
has_otype constructive_logic exists (arrow [universe, (arrow [X] bool)] bool).
has_otype constructive_logic falseP bool.
has_otype constructive_logic trueP bool.
has_otype constructive_logic iff (arrow [bool, bool] bool).
has_otype constructive_logic eq (arrow [X, X] bool).
has_otype constructive_logic neq (arrow [X, X] bool).
has_otype constructive_logic transitive (arrow [(arrow [X, X] bool)] bool).
has_otype constructive_logic xor (arrow [bool, bool] bool).
% has_otype constructive_logic ifthen (arrow [bool, X, X] X).

%% the OpenMath phrasebook entries for the constants:
%%==================================================
print_open_math_ and    "'OMS'(name:\"and\" cd:\"logic1\")".
print_open_math_ or     "'OMS'(name:\"or\" cd:\"logic1\")".
print_open_math_ imp    "'OMS'(name:\"implies\" cd:\"logic1\")".
print_open_math_ neg    "'OMS'(name:\"not\" cd:\"logic1\")".
print_open_math_ forall "'OMS'(name:\"forall\" cd:\"quant1\")".
print_open_math_ exists "'OMS'(name:\"exists\" cd:\"quant1\")".
print_open_math_ falseP "'OMS'(name:\"false\" cd:\"logic1\")".
print_open_math_ trueP  "'OMS'(name:\"true\" cd:\"logic1\")".
print_open_math_ iff    "'OMS'(name:\"equivalent\" cd:\"logic1\")".
print_open_math_ eq     "'OMS'(name:\"eq\" cd:\"relation1\")".
print_open_math_ neq    "'OMS'(name:\"neq\" cd:\"relation1\")".
print_open_math_ xor    "'OMS'(name:\"xor\" cd:\"logic1\")".

% logic1 CD: and, equivalent, false, implies, not, or, true, xor 
% relation1 CD: approx, eq, geq, gt, leq, lt, neq 

%%================================================

/* DEFINITIONS AND LEMMAS */

definition constructive_logic neq_eval trueP
     (app neq [X, Y]) (
     app neg [(app eq [X, Y])]).

/* maybe this should be a definition ? */
lemma constructive_logic idty equiv trueP (app eq [X, X]) trueP.

/* OTHER LEMMAS */

lemma constructive_logic assAnd1 equiv trueP (app and [A, (app and [B, C])]) 
                              (app and [(app and [A, B]), C]).

lemma constructive_logic prop3 equiv trueP  (app and [A, (app and [B, C])]) 
                             (app and [B, (app and [A, C])]).
lemma constructive_logic prop5 equiv trueP
   (app imp  [A,
           (app and [A, B])]) 
   (app imp [A, B]).

lemma constructive_logic prop6 equiv trueP (app or [A, (app and [B, C])]) 
                            (app and [(app or [A, B]),
                                             (app or [A, C])]).

% Probably shouldn't be here but don't know where else to put it.
% Abusing polarity here and using it to control rewriting.


axiom constructive_logic beta_idty equiv
	trueP
	(app eq [Y, (app (abs (x\ x) _) [Y])])
	trueP.

lemma constructive_logic prop4 rtol trueP
    (app imp [(app and [A, B]), (app and [A, C])]) 
    (app imp [B, C]).


% ifthen
%
definition constructive_logic ifthen1 C (app ifthen [C, X, _]) X.
definition constructive_logic ifthen1 (app neg [C])
	(app ifthen [C, _, Y]) Y.


/*
ATOMIC METHODS
*/

compound constructive_logic simple_eval_exi
	(orelse_meth
		(then_meth
			existential
			(try_meth (complete_meth sym_eval)))
		(complete_meth 
			(then_meth
				(then_meth (repeat_meth all_i) exists_i)
				sym_eval)))
	
	_
	true.


atomic constructive_logic existential
     ( seqGoal (H >>> (app exists [T2, (abs (x\ (Prop x)) T2)])) Context)
          true
          true
     ( (existsGoal T2 (Y\ (seqGoal
                 ( (( H >>> (Prop Y)) )) Context))))
          notacticyet.

% terminating cases:

atomic constructive_logic trivial
           (seqGoal ( H >>> G ) Context) 
           (memb (hyp G _) H) 
	   (instantiate_gb_context Context)
           trueGoal 
           notacticyet.
atomic constructive_logic trivial
           (seqGoal ( _H >>> trueP) Context) 
           true
	   (instantiate_gb_context Context)
           trueGoal 
           notacticyet.

local instantiate_gb_context (list context) -> o.
instantiate_gb_context Context:-
	memb_and_rest (unsure X RRINFO) Context Rest, !,
	for_each RRINFO (RINFO\ sigma Rule\ sigma Info\ sigma Used\ (
		RINFO = (rrstatus Rule Info Pointer Used),
		((not (Used = 0), fetch_rr_point Pointer Info (gbleaf good)); true))),
	instantiate_gb_context Rest.
instantiate_gb_context Context.

atomic constructive_logic trivially_false
           (seqGoal ( nil >>> falseP) _) 
           true
           true
           falseGoal 
           notacticyet.

atomic constructive_logic false_e
           (seqGoal ( H >>> _G ) Context) 
           (memb (hyp falseP _) H) 
	   (instantiate_gb_context Context)
           trueGoal
           notacticyet.

atomic constructive_logic false_e 
           (seqGoal ( H >>> _G ) Context) 
           (memb (hyp (app neq [X, X]) _) H) 
	   (instantiate_gb_context Context)
           trueGoal
           notacticyet.

atomic constructive_logic imp_i 
           (seqGoal (H >>> (app imp [A, B])) Context) 
	   true
           true 
           (seqGoal ((( (hyp A from_imp)::H) >>> B)) Context) 
           notacticyet.

atomic constructive_logic all_i 
           (seqGoal (H >>> (app forall [Otype, (abs A Otype)])) Context) 
	   true
           true 
           (allGoal Otype Y\ (seqGoal (((hyp (otype_of Y Otype) nha)::H) >>> (A Y)) Context)) 
           notacticyet.


atomic constructive_logic exists_i 
           (seqGoal (H >>> (app exists [Otype, (abs A Otype)])) Context) 
           true
           true 
           (existsGoal Otype Y\ (seqGoal (H >>> (A Y)) Context)) 
           notacticyet.

atomic constructive_logic exists_e 
           (seqGoal (H >>> G) Context) 
           (memb_and_rest (hyp (app exists [Otype, (abs A Otype)]) Ann) H R)
           true 
           (allGoal Otype Y\ (seqGoal (((hyp (otype_of Y Otype) witness_term)::((hyp (A Y) Ann)::R)) >>> G) Context)) 
           notacticyet.

atomic constructive_logic and_i 
           (seqGoal (H >>> (app and [A, B])) Context) 
           true 
           (update_gb_context ((seqGoal (H >>> A) Context) ** (seqGoal (H >>> B) Context)) NewGoals [])
	   NewGoals
           notacticyet.

atomic constructive_logic and_e 
           (seqGoal (H >>> G ) Context) 
           (memb (hyp (app and [A, B]) _) H, 
              replace_in_hyps H (hyp (app and [A, B]) Ann) ((hyp A Ann)::(hyp B Ann)::nil) HH
             )
           true
           (seqGoal (HH >>> G) Context)
           notacticyet.

atomic constructive_logic or_e 
            (seqGoal (H >>> G) Context)
            (memb (hyp (app or [A, B]) _) H,
             replace_in_hyps H (hyp (app or [A, B]) A1) ((hyp A A1)::nil) H1,
             replace_in_hyps H (hyp (app or [A, B]) A2) ((hyp B A2)::nil) H2, !)
            true
            ((seqGoal (H1 >>> G) Context) ** (seqGoal (H2 >>> G) Context))
            notacticyet.

% next, instead of Gentzens rule, use Roy Dyckhoffs versions from
% JSL 1992

atomic constructive_logic  ImpERule
            (seqGoal (H >>> G) Context) 
            (memb (hyp (app imp [X, B]) _) H)
            true 
            OutGoal 
            notacticyet:-
         impe_rule ImpERule X B (H >>> G) OutGoal Context, !.
              %% Warning !! last cut may lose completeness !!

atomic constructive_logic or_il 
	(seqGoal (H >>> (app or [A, _B])) Context) 
	true
	true
        (seqGoal (H >>> A) Context) 
	notacticyet.

atomic constructive_logic or_ir 
	(seqGoal (H >>> (app or [_A, B])) Context) 
	true 
	true
        (seqGoal (H >>> B) Context) 
	notacticyet.

atomic constructive_logic redundant
         (seqGoal (H >>> G) Context)
         (memb_and_rest (hyp (otype_of Var T) _) H Rest,
	  not (subterm_of G Var _),
	  not (memb (hyp Hyp _) Rest, subterm_of Hyp Var _))
         true  
	 (seqGoal (Rest >>> G) Context)
         notacticyet.

atomic constructive_logic redundant
         (seqGoal (H >>> G) Context)
         (replace_redundant G G1)	 
	 true
	 (seqGoal (H >>> G1) Context)
         notacticyet.

local replace_redundant osyn -> osyn -> o.
replace_redundant (app Quant [T, (abs (x\ (F x)) T)]) (app Quant [T, (abs (x\ (F1 x)) T)]):-
		  pi (x\ (has_otype constructive_logic x T => replace_redundant (F x) (F1 x))).
replace_redundant (app Quant [T, (abs (x\ F) T)]) F:-
		  (Quant = forall; Quant = exists).

atomic constructive_logic neg_i 
	(seqGoal (H >>> (app neg [B])) Context) 
	true
        true 
	(seqGoal ((( (hyp B nha)::H) >>> falseP)) Context) 
	notacticyet.

atomic constructive_logic neg_e 
	(seqGoal ( H >>> falseP ) Context) 
        ((memb (hyp (app neg [B]) _) H),
          replace_in_hyps H (hyp (app neg [B]) _) nil H1)
        true
        (seqGoal ( H1 >>> B ) Context)
        notacticyet.

/*  
SUPPORT FOR imp_rule
*/

% recognize atomic formulas

atomic_term(app and [_X, _Y]) :- fail, !.
atomic_term(app or [_X,  _Y]) :- fail, !.
atomic_term(app imp [_X, _Y]) :- fail, !.
atomic_term(app forall _Y ) :- fail, !.
atomic_term(app exists _Y ) :- fail, !.
atomic_term falseP :- fail, !.      % ! see Dyckhoffs article.
atomic_term( _ ) :- true.             % anything else ....



impe_rule imp_e1 A B (H >>> G) (seqGoal (HH >>> G) Context) Context:-
          memb (hyp A _) H,
          atomic_term A,
          replace_in_hyps H (hyp (app imp [A, B]) Ann) ((hyp B Ann)::nil) HH, !.

impe_rule imp_e2 (app and [C, D]) B (H >>> G) (seqGoal (HH >>> G) Context) Context:-
          replace_in_hyps H (hyp (app imp [(app and [C, D]), B]) Ann)
                 ((hyp (app imp [C, (app imp [D, B])]) Ann)::nil) HH, !.


impe_rule imp_e3 (app or [C, D]) B (H >>> G) (seqGoal (HH >>> G) Context) Context:-
          replace_in_hyps H (hyp (app imp [(app or [C, D]), B]) Ann)
               ((hyp (app imp [C, B]) Ann)::(hyp (app imp [D, B]) Ann)::nil) HH, !.

impe_rule imp_e4 (app imp [C, D]) B (H >>> G) 
      ((seqGoal (HH >>> G) Context) ** (seqGoal (HHH >>> (app imp [C, D])) Context)) Context:-
       replace_in_hyps H (hyp (app imp [(app imp [C, D]), B]) Ann)
                ((hyp B Ann)::nil) HH, 
      replace_in_hyps H (hyp (app imp [(app imp [C, D]), B]) Ann)
                ((hyp (app imp [D, B]) Ann)::nil) HHH.

% Reintroduce foralls after induction - no backtracking
atomic constructive_logic all_e
        (seqGoal (H >>> G) Context)
        (memb_and_rest (hyp (otype_of X T) _) H NewH, 
	 subterm_of G X _,
	 (not (memb (hyp K An) NewH, subterm_of K X _)), 
         forall_elim X T G NewG,
         (not (subterm_of NewG X _)))
        true
        (seqGoal (NewH >>> NewG) Context)
        notacticyet.

atomic constructive_logic allFi 	
	(seqGoal (H >>> (app forall [(arrow A B), (abs F (arrow A B))])) Context)
        true true
        (allGoal (arrow A B) (p\ (seqGoal (((hyp (otype_of p (arrow A B)) nha)::H) >>> (F p)) Context)) )
        notacticyet.


compound constructive_logic taut
      (complete_meth
         (repeat_meth
           (orelse_meth trivial
            (orelse_meth false_e
            (orelse_meth neg_i
            (orelse_meth neg_e
            (orelse_meth imp_i
            (orelse_meth all_i	
            (orelse_meth exists_i 
            (orelse_meth and_i
            (orelse_meth and_e
            (orelse_meth or_e
            (orelse_meth imp_e1
            (orelse_meth imp_e2
            (orelse_meth imp_e3
            (orelse_meth imp_e4
            (orelse_meth or_il or_ir)))))))))))))))))
	_
	true.

%% A couple of easy tautologies

top_goal constructive_logic taut1 [] (app imp [obj, obj]).
top_goal constructive_logic taut2 [] (app forall [bool, (abs (P\ (app neg [(app and [P, (app neg [P])])])) bool)]). 



end
