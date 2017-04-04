/*

File: objlists.mod
Author: Louise Dennis
Description: A Theory for Lists
Last Modified: 20th March 2001

*/

module objlists.

accumulate arithmetic.

% Basic rewrites
% 

lemma objlists cons_functional equiv trueP 
(app eq [(app ocons [X, Y]), (app ocons [W, Z])]) 
(app and [(app eq [X, W]), (app eq [Y, Z])]).

definition objlists oapp1 trueP (app oapp [onil, Y]) Y. 
definition objlists oapp2 trueP (app oapp [(app ocons [X, Y]), Z]) (app ocons [X, (app oapp [Y, Z])]).
lemma objlists ass_oapp equiv trueP  (app oapp [(app oapp [X, Y]), Z]) (app oapp [X, (app oapp [Y, Z])]). 


% olength
%
% (olength onil) => zero.
definition objlists olength1 trueP (app olength [onil]) zero.
%
% (olength (ocons H T)) => (s (olength T)). 
definition objlists olength2 trueP (app olength [(app ocons [_H, T])]) (app s [(app olength [T])]).

% orev - these need extra otype_of's on RHSs.
% '
% (orev onil) => onil
definition objlists orev1  trueP 
    (app orev [onil] ) 
    onil.
%
% (orev (ocons H T)) => (oapp (orev T) (ocons H onil)).
definition objlists orev2  trueP   
    (app orev [(app ocons [H, T])]) 
    (app oapp [(app orev [T]),
                    (app ocons [H, onil])]).


definition objlists allList1 trueP 
       (app allList [_X, onil]) 
       trueP.

definition objlists allList2 trueP 
       (app allList [(abs (X\ (F X)) Type), (app ocons [H, T])]) 
       (app and [(F H), (app allList [(abs (X\ (F X)) Type), T])]).

lemma  objlists allList_or_l rtol trueP 
     (app allList [
       (abs (x\ (app or [(P x), (_Q x)])) Type), L])
     (app allList [(abs P Type), L]).

lemma objlists allList_or_r rtol trueP 
     (app allList [
       (abs (x\ (app or [(_P x), (Q x)])) Type),
       L])
     (app allList [(abs Q Type), L]).



% Two step list induction
%
induction_scheme  objlists list_twostep
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
induction_scheme  objlists list_struct
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

is_otype objlists (olist X) [onil] [ocons].

has_otype objlists onil (olist _X).
has_otype objlists ocons (arrow [X, (olist X)] (olist X)).
has_otype objlists oapp (arrow [(olist X), (olist X)] (olist X)).
has_otype objlists olength (arrow [(olist _X)] nat). 
has_otype objlists orev    (arrow [(olist X)] (olist X)). 
has_otype objlists allList (arrow [(arrow [X] bool), (olist X)] bool). 
% simple list theory
% 
top_goal objlists assapp []
     (app forall [(olist nat), 
          (abs (x\ (app forall [(olist nat),  
          (abs (y\ (app forall [(olist nat), 
          (abs (z\ (app eq [(app oapp [(app oapp [x, y]),  z]),  (app oapp [x, (app oapp [y, z])])])) (olist nat))])) (olist nat))])) (olist nat))]).




% Higher-order in that it requires correct manipulation of lambda binders
% but does not really need any manipulation of the functions themselves.
% Ripples out 7 times then strong fertilises.
%
top_goal objlists all_list []
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
top_goal objlists all_list_sy []
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
top_goal objlists all_list_cv []
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
top_goal objlists allList_and_dist []
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
top_goal objlists allList_and_dist_cv []
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
top_goal objlists allList_or_left []
  (app forall [(arrow [obj] bool),
   (abs (P\ (app forall [(arrow [obj] bool),
    (abs (Q\ (app forall [(olist obj),
     (abs (l\ (app imp [(app allList [(abs (x\ (app P [x])) obj), l]), 
                       (app allList [(abs (x\ (app or [(app P [x]), (app Q [x])])) obj), 
         l])])) (olist obj))])) (arrow [obj] bool))])) (arrow [obj] bool))]).

% solved
%
top_goal objlists allList_or_right []
   (app forall [(arrow [obj] bool),
     (abs (P\ (app forall [(arrow [obj] bool),
       (abs (Q\ (app forall [(olist obj),
        (abs (l\ (
            (app imp [(app allList [(abs (x\ (app Q [x])) obj), l]), 
                           (app allList [
                                 (abs (x\ (app or [(app P [x]),
                                                        (app Q [x])])) obj), 
                                          l])]))) (olist obj))])) (arrow [obj] bool))])) (arrow [obj] bool))]).





end
