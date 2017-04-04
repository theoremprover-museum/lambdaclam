/*

File: ccs_hmf_theory.mod
Author: James Brotherston
Description: CCS / Hennessy-Milner logic examples from Stirling 2001
Last Modified: 26th July 2002

*/

module ccs_hmf_theory.

accumulate ccs_hmf_methods.

local ccs_hmf_dummy o -> o.
ccs_hmf_dummy X.

%% Definition of clock process, Cl 

has_otype ccs_hmf_theory cl ccs.
has_otype ccs_hmf_theory tick action.
has_otype ccs_hmf_theory tock action.

definition ccs_hmf_theory cl_def trueP cl 
  (app dot (tuple [tick,cl])).


%% Definition of vending machine process, Ven

has_otype ccs_hmf_theory ven ccs.
has_otype ccs_hmf_theory ven_b ccs.
has_otype ccs_hmf_theory ven_l ccs.
has_otype ccs_hmf_theory a1p action.
has_otype ccs_hmf_theory a2p action.
has_otype ccs_hmf_theory big action.
has_otype ccs_hmf_theory little action.
has_otype ccs_hmf_theory collect_b action.
has_otype ccs_hmf_theory collect_l action.

definition ccs_hmf_theory cl_def trueP ven 
  (app ccs_plus (tuple [(app dot (tuple [a2p, ven_b])),
		    (app dot (tuple [a1p, ven_l]))])).

definition ccs_hmf_theory cl_def trueP ven_b
  (app dot (tuple [big,
    (app dot (tuple [collect_b, ven]))])).

definition ccs_hmf_theory cl_def trueP ven_l
  (app dot (tuple [little,
    (app dot (tuple [collect_l, ven]))])).


%% Definition of parallel counting process, Cnt

has_otype ccs_hmf_theory cnt ccs.
has_otype ccs_hmf_theory up action.
has_otype ccs_hmf_theory down action.

definition ccs_hmf_theory cnt_def trueP cnt
  (app dot (tuple [up,
    (app bar (tuple [cnt,
      (app dot (tuple [down, ccs_nil]))]))])).

%% Definition of parameterised counting process, Ct(i)

has_otype ccs_hmf_theory ct (nat arrow ccs).
has_otype ccs_hmf_theory round action.

definition ccs_hmf_theory ct0_def trueP (app ct zero)
  (app ccs_plus (tuple [
    (app dot (tuple [up, (app ct (app s zero))])),
    (app dot (tuple [round, (app ct zero)]))])).

definition ccs_hmf_theory ct0_def trueP (app ct (app s I))
  (app ccs_plus (tuple [
    (app dot (tuple [up, (app ct (app s (app s I)))])),
    (app dot (tuple [down, (app ct I)]))])).


%% Definition of level crossing process, Crossing, and auxiliaries

has_otype ccs_hmf_theory crossing ccs.
has_otype ccs_hmf_theory road ccs.
has_otype ccs_hmf_theory rail ccs.
has_otype ccs_hmf_theory signal ccs.
has_otype ccs_hmf_theory car action.
has_otype ccs_hmf_theory ccross action.
has_otype ccs_hmf_theory train action.
has_otype ccs_hmf_theory tcross action.
has_otype ccs_hmf_theory green action.
has_otype ccs_hmf_theory orange action.

definition ccs_hmf_theory crossing_def trueP crossing
  (app slash (tuple [
    (app bar (tuple [road,
      (app bar (tuple [rail,signal]))])),
    (app ocons (tuple [green,
      (app ocons (tuple [orange,
        (app ocons (tuple [up,
          (app ocons (tuple [down,onil]))]))]))]))])).

definition ccs_hmf_theory road_def trueP road
  (app dot (tuple [car, 
    (app dot (tuple [up,
      (app dot (tuple [ccross,
	(app dot (tuple [(app co down),road]))]))]))])).

definition ccs_hmf_theory rail_def trueP rail
  (app dot (tuple [train, 
    (app dot (tuple [green,
      (app dot (tuple [tcross,
	(app dot (tuple [(app co orange),rail]))]))]))])).

definition ccs_hmf_theory rail_def trueP signal
  (app ccs_plus (tuple [
    (app dot (tuple [(app co green),
      (app dot (tuple [orange, signal]))])),
    (app dot (tuple [(app co up),
      (app dot (tuple [down, signal]))]))])).


%% Definition of multiple copier, Cop' and parameterised auxiliary Cop(i,x)

has_otype ccs_hmf_theory cop' ccs.
has_otype ccs_hmf_theory cop (tuple_type [nat,nat] arrow ccs).
has_otype ccs_hmf_theory in action.
has_otype ccs_hmf_theory out action.
has_otype ccs_hmf_theory no action.

definition ccs_hmf_theory cop'_def trueP cop'
  (app dot (tuple [(app no N),
    (app dot (tuple [(app in X), (app cop (tuple [N,X]))]))])).

definition ccs_hmf_theory cop_def1 trueP (app cop (tuple [zero,X]))
  (app dot (tuple [(app out X), cop'])).

definition ccs_hmf_theory cop_def2 trueP (app cop (tuple [(app s N),X]))
  (app dot (tuple [(app out X), (app cop (tuple [N,X]))])).


%% Examples from Stirling's book, chapter 2
	
top_goal ccs_hmf_theory cl_ex1 []
  (app satisfies (tuple [cl,
   (app box (tuple [(app ocons (tuple [tick,onil])),
    (app and (tuple [
      (app diamond (tuple [(app ocons (tuple [tick,onil])), tt])),
      (app box (tuple [(app ocons (tuple [tock,onil])), ff]))]))]))])).

top_goal ccs_hmf_theory ven_ex1 []
  (app satisfies (tuple [ven,
   (app box (tuple [(app ocons (tuple [a2p,onil])),
    (app and (tuple [
      (app box (tuple [(app ocons (tuple [little,onil])), ff])),
      (app diamond (tuple [(app ocons (tuple [big,onil])), tt]))]))]))])).

top_goal ccs_hmf_theory ven_ex2 []
   (app satisfies (tuple [ven,
     (app box (tuple [(app ocons (tuple [a1p, 
			(app ocons (tuple [a2p,onil]))])),
       (app box (tuple [(app ocons (tuple [a1p, 
			(app ocons (tuple [a2p,onil]))])), ff]))]))])).

top_goal ccs_hmf_theory ven_ex3 []
   (app satisfies (tuple [ven,
     (app box (tuple [(app ocons (tuple [a1p, 
			(app ocons (tuple [a2p,onil]))])),
     (app box (tuple [(app ocons (tuple [big, 
			(app ocons (tuple [little,onil]))])), 
     (app diamond (tuple [(app ocons (tuple [collect_b,
			(app ocons (tuple [collect_l, onil]))])), 
      tt]))]))]))])).

top_goal ccs_hmf_theory ven_ex4 []
   (app satisfies (tuple [ven,
     (app box (tuple [(app ocons (tuple [a2p,onil])),
       (app and (tuple [
         (app box (tuple [(app ocons (tuple [allminus, 
            		  (app ocons (tuple [big,onil]))])), ff])),
	 (app diamond (tuple [(app ocons (tuple [allminus,
			      (app ocons (tuple [little,
			      (app ocons (tuple [a2p,onil]))]))])), tt]
	))]))]))])).

top_goal ccs_hmf_theory cnt_ex1 []
   (app satisfies (tuple [cnt,
     (app box (tuple [(app ocons (tuple [up,onil])),
       (app diamond (tuple [(app ocons (tuple [down,onil])),
	 (app box (tuple [(app ocons (tuple [down,onil])), ff]
   ))]))]))])).

top_goal ccs_hmf_theory crossing_ex1 []
   (app satisfies (tuple [crossing,
     (app box (tuple [(app ocons (tuple [train,onil])),
       (app and (tuple [
         (app diamond (tuple [(app ocons (tuple [tau,onil])), tt])),
         (app diamond (tuple [(app ocons (tuple [car,onil])),
           (app box (tuple [(app ocons (tuple [tau,onil])),
             (app box (tuple [(app ocons (tuple [tau,onil])), 
             ff]))]))]))]))]))])).

top_goal ccs_hmf_theory crossing_ex2 []
   (app satisfies (tuple [crossing,
     (app box (tuple [(app ocons (tuple [car,onil])),
       (app box (tuple [(app ocons (tuple [train,onil])),
         (app box (tuple [(app ocons (tuple [tau,onil])),
           (app or (tuple [
             (app diamond (tuple [(app ocons (tuple [tcross,onil])), tt])),
             (app diamond (tuple [(app ocons (tuple [ccross,onil])), tt]))
     ]))]))]))]))])).
       
%% Parameterised examples - prove by induction on naturals

top_goal ccs_hmf_theory cop_ex1 []
  (app forall (tuple [nat, (abs i\
   (app forall (tuple [nat, (abs v\ 
    (app satisfies (tuple [cop',
     (app box (tuple [(app ocons (tuple [(app no i),onil])),
      (app box (tuple [(app ocons (tuple [(app in v),onil])),
       (app exp_diamond (tuple [(app ocons (tuple [(app out v),onil])), 
                                (app s i), tt]))]))]))])))])))])).

top_goal ccs_hmf_theory ct_lem1 []
  (app forall (tuple [nat, (abs j\
   (app forall (tuple [nat, (abs i\ 
    (app satisfies (tuple [(app ct (app plus (tuple [j,i]))),
     (app exp_diamond (tuple [(app ocons (tuple [down,onil])), j, tt]
   ))])))])))])).

top_goal ccs_hmf_theory ct_lem2 []
  (app forall (tuple [nat, (abs i\
   (app forall (tuple [ccs, (abs phi\
    (app imp (tuple [
     (app satisfies (tuple [(app ct (app s i)), phi])),
     (app satisfies (tuple [(app ct i),
      (app box (tuple [(app ocons (tuple [up,onil])), phi]))]))])))])))])).

top_goal ccs_hmf_theory ct_lem3 []
  (app forall (tuple [nat, (abs j\
   (app forall (tuple [nat, (abs i\
    (app forall (tuple [ccs, (abs phi\
     (app imp (tuple [
      (app satisfies (tuple [(app ct (app plus (tuple [j,i]))), phi])),
      (app satisfies (tuple [(app ct i),
       (app exp_box (tuple [(app ocons (tuple [up,onil])), j, phi
  ]))]))])))])))])))])).

%% The following lemma is needed for ct_lem3

lemma ccs_hmf_theory plus_lem1 ltor trueP
  (app plus (tuple [(app s J),I]))
  (app plus (tuple [J,(app s I)])).

%% Top goals ct_lem1 and ct_lem3 are used to prove the next top goal

top_goal ccs_hmf_theory ct_ex1 []
  (app forall (tuple [nat, (abs i\
   (app forall (tuple [nat, (abs j\
    (app satisfies (tuple [(app ct i),
     (app exp_box (tuple [(app ocons (tuple [up,onil])), j,
      (app exp_diamond (tuple [(app ocons (tuple [down,onil])), j, tt]
     ))]))])))])))])).

%% First structural induction example

top_goal ccs_hmf_theory hmf_comp1 []
  (app forall (tuple [hmf, (abs phi\
   (app eq (tuple [(app hmf_comp (app hmf_comp phi)), phi])))])).


end