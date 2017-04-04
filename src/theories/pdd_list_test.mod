/*

File: objlists.mod
Author: Louise Dennis
Description: A Theory for Lists
Last Modified: 20th March 2001

*/

module pdd_list_test.

accumulate pdd_test_arith.

local pdddummy osyn -> o.
pdddummy X.

% Basic rewrites
% 

lemma pdd_list_test cons_functional equiv trueP 
(app eq [(app ocons [X, Y]), (app ocons [W, Z])]) 
(app and [(app eq [X, W]), (app eq [Y, Z])]).

has_otype pdd_list_test o1app (arrow [(olist X), (olist X)] (olist X)).
has_otype pdd_list_test o2app (arrow [(olist X), (olist X)] (olist X)).
has_otype pdd_list_test o3app (arrow [(olist X), (olist X)] (olist X)).
has_otype pdd_list_test o4app (arrow [(olist nat), (olist nat)] (olist nat)).

has_otype pdd_list_test removeAll (arrow [X, (olist X)] (olist X)).
has_otype pdd_list_test removeOne (arrow [X, (olist X)] (olist X)).

known_false (app eq [onil, (app ocons [X, Y])]).
known_false (app eq [(app ocons [X, Y]), onil]).

definition pdd_list_test removeOne1 trueP
	(app removeOne [_, onil])
	onil.
definition pdd_list_test removeOne2 trueP
	(app removeOne [X, (app ocons [X, T])])
	T.
definition pdd_list_test removeOne3 (app neq [X, Y])
	(app removeOne [X, (app ocons [Y, T])])
	(app ocons [Y, (app removeOne [X, T])]).


definition pdd_list_test removeAll1 trueP
	(app removeAll [_, onil])
	onil.
definition pdd_list_test removeAll2 trueP
	(app removeAll [X, (app ocons [X, T])])
	(app removeAll [X, T]).
definition pdd_list_test removeAll3 (app neq [X, Y])
	(app removeAll [X, (app ocons [Y, T])])
	(app ocons [Y, (app removeOne [X, T])]).

definition pdd_list_test omem1 trueP (app omember  [_X,  onil]) falseP.
definition pdd_list_test omem2 (app neq  [X, Y])
    (app omember  [X, (app ocons  [Y, Z])])
    (app omember  [X, Z]).
definition pdd_list_test omem3 trueP
    (app omember  [X, (app ocons  [X, Z])])
    (trueP).


definition pdd_list_test o1app2 trueP 
	   (app o1app [(app ocons [X, Y]), Z]) 
	   (app ocons [X, (app o1app [Y, Z])]).

definition pdd_list_test o2app1 trueP 
	   (app o2app [onil, Z]) 
	   (app orev [Z]).
definition pdd_list_test o2app2 trueP 
	   (app o2app [(app ocons [X, Y]), Z]) 
	   (app ocons [X, (app o2app [Y, Z])]).

definition pdd_list_test o4app1 trueP 
	   (app o4app [onil, Z]) 
	   (app ocons [zero, onil]).
definition pdd_list_test o4app2 trueP 
	   (app o4app [(app ocons [X, Y]), Z]) 
	   (app ocons [X, (app o4app [Y, Z])]).

definition pdd_list_test o3app1 trueP 
	   (app o3app [onil, Z]) 
	   Z.
definition pdd_list_test o3app2 trueP 
	   (app o3app [(app ocons [X, Y]), Z]) 
	   (app ocons [X, (app ocons [X, (app o3app [Y, Z])])]).

top_goal_c pdd_list_test assapp1 []
     (app forall [(olist nat),
          (abs (x\ (app forall [(olist nat),
          (abs (y\ (app forall [(olist nat),
          (abs (z\ (app eq [(app o1app [(app o1app [x, y]),  z]),  (app o1app [x, (app o1app [y, z])])])) (olist nat))])) (olist nat))])) (olist nat))]) [(unsure o1app [(rrstatus o1app2 Tree [] Used)]), (banned [oapp1, oapp2, o2app1, o2app2, o3app1, o3app2, o4app1, o4app2])].
%% error located and repaired.

top_goal_c pdd_list_test removeAllthm []
     (app forall [nat,
          (abs (x\ (app forall [(olist nat),
          (abs (l\ (app neg [(app omember [x, (app removeAll [x, l])])])) (olist nat))])) nat)])
[(unsure removeAll [(rrstatus removeAll1 Tree1 [] Used1),
(rrstatus removeAll2 Tree2 [] Used2),
(rrstatus removeAll2 Tree3 [] Used3)]),
(unsure removeOne [(rrstatus removeOne1 Tree4 [] Used4),
(rrstatus removeOne2 Tree5 [] Used5),
(rrstatus removeOne2 Tree6 [] Used6)]),
(banned [oapp1, oapp2, o2app1, o2app2, o3app1, o3app2, o4app1, o4app2])].
%% error located and repaired.

top_goal_c pdd_list_test assapp2 []
     (app forall [(olist nat),
          (abs (x\ (app forall [(olist nat),
          (abs (y\ (app forall [(olist nat),
          (abs (z\ (app eq [(app o2app [(app o2app [x, y]),  z]),  
                  (app o2app [x, (app o2app [y, z])])])) (olist nat))])) (olist nat))])) (olist nat))]) 
       [(unsure o2app [(rrstatus o2app1 Tree1 [] Used1), 
                       (rrstatus o2app2 Tree2 [] Used2)]),
        (unsure orev [(rrstatus orev1 Tree3 [] Used3), 
                      (rrstatus orev2 Tree4 [] Used4)]), 
        (banned [oapp1, oapp2, o1app2, o3app1, o3app2, o4app1, o4app2])].


top_goal_c pdd_list_test assapp3 []
     (app forall [(olist nat),
          (abs (x\ (app forall [(olist nat),
          (abs (y\ (app forall [(olist nat),
          (abs (z\ (app eq [(app o3app [(app o3app [x, y]),  z]),  (app o3app [x, (app o3app [y, z])])])) (olist nat))])) (olist nat))])) (olist nat))]) [(unsure o3app [(rrstatus o3app1 Tree1 [] Used1), (rrstatus o3app2 Tree2 [] Used2)]), (banned [oapp1, oapp2, o2app1, o2app2, o1app2, o4app1, o4app2])].
%% error located and repaired.

top_goal_c pdd_list_test assapp4 []
     (app forall [(olist nat),
          (abs (x\ (app forall [(olist nat),
          (abs (y\ (app forall [(olist nat),
          (abs (z\ (app eq [(app o4app [(app o4app [x, y]),  z]),  (app o4app [x, (app o4app [y, z])])])) (olist nat))])) (olist nat))])) (olist nat))]) [(unsure o4app [(rrstatus o4app1 Tree1 [] Used1), (rrstatus o4app2 Tree2 [] Used2)]), (banned [oapp1, oapp2, o2app1, o2app2, o3app1, o3app2, o1app2])].
%% error located and repaired.

% olength
%
% (olength onil) => zero.
definition pdd_list_test olength1 trueP (app olength [onil]) zero.
%
% (olength (ocons H T)) => (s (olength T)). 
definition pdd_list_test olength2 trueP (app olength [(app ocons [_H, T])]) (app s [(app olength [T])]).

% orev - these need extra otype_of's on RHSs.
% '
% (orev onil) => onil
definition pdd_list_test orev1  trueP 
    (app orev [onil] ) 
    onil.
%
% (orev (ocons H T)) => (oapp (orev T) (ocons H onil)).
definition pdd_list_test orev2  trueP   
    (app orev [(app ocons [H, T])]) 
    (app oapp [(app orev [T]),
                    (app ocons [H, onil])]).


definition pdd_list_test allList1 trueP 
       (app allList [_X, onil]) 
       trueP.

definition pdd_list_test allList2 trueP 
       (app allList [(abs X Type), (app ocons [H, T])]) 
       (app and [(X H), (app allList [(abs X Type), T])]).

lemma  pdd_list_test allList_or_l rtol trueP 
     (app allList [
       (abs (x\ (app or [(P x), (_Q x)])) Type), L])
     (app allList [(abs P Type), L]).

lemma pdd_list_test allList_or_r rtol trueP 
     (app allList [
       (abs (x\ (app or [(_P x), (Q x)])) Type),
       L])
     (app allList [(abs Q Type), L]).



% Two step list induction
%
induction_scheme  pdd_list_test list_twostep
   % Info
   (olist T)
   (dom a\ (dom b\ (dom c\ (repl c (app ocons [a, (app ocons [b, c])])))))
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall [(olist T), (abs Prop (olist T))])) Context)
   % Step cases
   (
    (allGoal (olist T) (t\ (allGoal T (h\ (allGoal T (i\ (seqGoal ((
		            (hyp (otype_of h T) nha)::
                            (hyp (otype_of i T) nha)::
                            (hyp (otype_of t (olist T)) nha)::
                            (hyp (Prop t) ind_hyp)::H)
                          >>>
                          (Prop (app ocons [h, (app ocons [i, t])]))) Context)))))))
   % Base case
    **
     ((seqGoal (H >>> (Prop onil)) Context)
     ** 
     (allGoal T (s\ (seqGoal (((hyp (otype_of s T) nha)::H)
                           >>> (Prop (app ocons [s, onil] ))) Context))))
	).

% Structural induction for lists.
induction_scheme  pdd_list_test list_struct
   % Info
   (olist T)
   (dom (b \ (dom (c \ (repl c (app ocons [b, c]))))))
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall [(olist T), (abs Prop (olist T))])) Context)
   % Step case
   (
    (allGoal (olist T)
    t\ (allGoal T
    h\ (seqGoal (((hyp (otype_of h T) nha)::
               (hyp (otype_of t (olist T)) nha)::
               (hyp (Prop t) ind_hyp)::H)
          >>> (Prop (app ocons [h, t]))) Context)))
    **
   % Base case
	(seqGoal (H >>> (Prop onil)) Context)
	).






%
% Object level types
%

is_otype pdd_list_test (olist X) [onil] [ocons].

has_otype pdd_list_test onil (olist _X).
has_otype pdd_list_test ocons (arrow [X, (olist X)] (olist X)).
has_otype pdd_list_test oapp (arrow [(olist X), (olist X)] (olist X)).
has_otype pdd_list_test olength (arrow [(olist _X)] nat). 
has_otype pdd_list_test orev    (arrow [(olist X)] (olist X)). 
has_otype pdd_list_test allList (arrow [(arrow [X] bool), (olist X)] bool). 
% simple list theory
% 
top_goal pdd_list_test assapp []
     (app forall [(olist nat), 
          (abs (x\ (app forall [(olist nat),  
          (abs (y\ (app forall [(olist nat), 
          (abs (z\ (app eq [(app oapp [(app oapp [x, y]),  z]),  (app oapp [x, (app oapp [y, z])])])) (olist nat))])) (olist nat))])) (olist nat))]).




% Higher-order in that it requires correct manipulation of lambda binders
% but does not really need any manipulation of the functions themselves.
% Ripples out 7 times then strong fertilises.
%
top_goal pdd_list_test all_list []
   (app forall [(olist nat),
     (abs (l\ (app forall [(arrow [nat] bool),
       (abs (P\ (app forall [(arrow [nat] bool),
          (abs (Q\ (app imp [
               (app and [
                      (app allList [(abs (x\ (app P [x])) nat), l]),
                      (app allList [(abs (x\ (app Q [x])) nat), l])] ) ,
               (app allList [ 
                       (abs (x\ (app and [(app P [x]), (app Q [x])])) nat),
                        l])] )) (arrow [nat] bool))])) (arrow [nat] bool))])) (olist nat))]).

% Higher order and requires care with rewriting in the presence of a 
% meta-variable.
%
top_goal pdd_list_test all_list_sy []
   (app forall [(arrow [obj] bool),
    (abs (P\ (app forall [(arrow [obj] bool),
     (abs (Q\ (app exists [(arrow [obj] bool),
      (abs (R\ (app forall [(olist obj),
       (abs (l\ (app imp [(app and [
           (app allList [P, l]),
           (app allList [Q, l])]), 
         (app allList [R, l])])) (olist obj) )])) (arrow [obj] bool))])) (arrow [obj] bool))])) (arrow [obj] bool))]).

% all_list_u ( forall2 P\ (forall2 Q\ (forall (olist obj) l\ (
%    (((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool))P l) or ((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) Q l)) (otype_of imp ((pair_type bool bool) arrow bool)) 
%          ((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) (x\ ((P x) or (Q x))) l) )))).

% solved
%
top_goal pdd_list_test all_list_cv []
   (app forall [(arrow [obj] bool),
    (abs (P\ (app forall [(arrow [obj] bool),
     (abs (Q\ (app forall [(olist obj),
      (abs (l\ ((app imp [
               (app allList [
                     (abs (x\ (app and [(app P [x]), (app Q [x])])) obj), l]),
          (app and [(app allList [(abs (x\ (app P [x])) obj), l]), 
                         (app allList [(abs (x\ (app Q [x])) obj), l])])]))) (olist obj))]
              )) (arrow [obj] bool))])) (arrow [obj] bool))]).

%all_list_cv_sy ( (otype_of forall ((obj arrow bool) arrow bool)) P\ ((otype_of forall ((obj arrow bool) arrow bool)) Q\ exists2 R\ (forall (olist obj) l\ (((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) R l) (otype_of imp ((pair_type bool bool) arrow bool))
%                (((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) P l) (otype_of and ((pair_type bool bool) arrow bool)) ((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) Q l))
%              )))).

% Three theorems from BBN 1163, section 3.
%
% solved
%
top_goal pdd_list_test allList_and_dist []
   (app forall [(arrow [obj] bool),
    (abs (P\ (app forall [(arrow [obj] bool),
     (abs (Q\ (app forall [(olist obj),
      (abs (l\ 
       (app imp [(app allList [
                 (abs (x\ (app and [(app P [x]), (app Q [x])])) obj), 
                  l]),  
             (app and [
                  (app allList [(abs (x\ (app P [x])) obj), l]),
                  (app allList [(abs (x\ (app Q [x])) obj), l])])])) (olist obj))])) (arrow [obj] bool))])) (arrow [obj] bool))]).

% solved
%
top_goal pdd_list_test allList_and_dist_cv []
  (app forall [(arrow [obj] bool),
   (abs (P\ (app forall [(arrow [obj] bool),
    (abs (Q\ (app forall [(olist obj),
     (abs (l\ 
      (app imp [(app and [(app allList [(abs (x\ (app P [x])) obj), l]), 
                       (app allList [(abs (x\ (app Q [x])) obj), l])]), 
                 (app allList [(abs (x\ (app and [(app P [x]), (app Q [x])])) obj),
                                         l])])) (olist obj))])) (arrow [obj] bool))])) (arrow [obj] bool))]).

% solved
%
top_goal pdd_list_test allList_or_left []
  (app forall [(arrow [obj] bool),
   (abs (P\ (app forall [(arrow [obj] bool),
    (abs (Q\ (app forall [(olist obj),
     (abs (l\ (app imp [(app allList [(abs (x\ (app P [x])) obj), l]), 
                       (app allList [(abs (x\ (app or [(app P [x]), (app Q [x])])) obj), 
         l])])) (olist obj))])) (arrow [obj] bool))])) (arrow [obj] bool))]).

% solved
%
top_goal pdd_list_test allList_or_right []
   (app forall [(arrow [obj] bool),
     (abs (P\ (app forall [(arrow [obj] bool),
       (abs (Q\ (app forall [(olist obj),
        (abs (l\ (
            (app imp [(app allList [(abs (x\ (app Q [x])) obj), l]), 
                           (app allList [
                                 (abs (x\ (app or [(app P [x]),
                                                        (app Q [x])])) obj), 
                                          l])]))) (olist obj))])) (arrow [obj] bool))])) (arrow [obj] bool))]).



benchmark_plan pdd_list_test Meth Query :-
	       testloop (%interaction_mode command,
	       (set_theory_induction_scheme_list pdd_list_test,
	       (add_theory_to_induction_scheme_list pdd_test_arith,
	       (set_sym_eval_list [and3, and4, idty, s_functional, cons_functional, leq1, leq2, leq_ss, assAnd1, prop3, prop4, prop5, prop6, andlem],
	       	(add_theory_defs_to_sym_eval_list pdd_test_arith,
		(add_theory_defs_to_sym_eval_list pdd_list_test,
		(add_theory_defs_to_sym_eval_list pdd_repair,
	       (set_wave_rule_to_sym_eval,
	       (add_to_sym_eval_list [beta_reduction],
	       pds_plan Meth Query))))))))).


end
