module pdd_nominate_app2_nowave.

accumulate constructive_logic.
accumulate pdd_nominate.

%
% Object level types
%

/* Results

assapp - app1 0,1 app2 1,0
app1right -true.
cnc_app - true.
comapp - app1 0,2 app2 1,1
memapp2 - piecewise fertilisation diverges
memapp3 - true but omem1, 0,1, omem2 1,0, omem3, 0, 1 app1 0,1 oapp2 1,0
memapp true but omem2 1,0, omem3 0,1 oapp2 1,0
countsort
lensort
memins
meminsert1
meminsert2
memsort1
memsort2
ordered_cons

assapp - app1 , 0,1
      - same.
comapp app1 0,2 app1 0,1
      - same
memapp3 omem1 0,1 omem3 0,1 oapp1 01 oapp2 01 (true)
memapp (true)

*/

local pnt osyn -> o.
pnt X:- printstdout X.
local pnt2 osyn -> o.
pnt2 X.
local pnt3 osyn -> o.
pnt3 X.

is_otype pdd_nominate_tests (olist X) [onil] [ocons].

has_otype pdd_nominate_tests onil (olist _X).
has_otype pdd_nominate_tests ocons (arrow [X, (olist X)] (olist X)).
has_otype pdd_nominate_tests oapp (arrow [(olist X), (olist X)] (olist X)).
has_otype pdd_nominate_tests sort (arrow [(olist nat)] (olist nat)).
has_otype pdd_nominate_tests insert (arrow [nat, (olist nat)](olist nat)).
has_otype pdd_nominate_tests count (arrow [X, (olist X)] nat).
has_otype pdd_nominate_tests ordered (arrow [(olist nat)] bool).
has_otype pdd_nominate_tests omember (arrow [X, (olist X)] bool).
has_otype pdd_nominate_tests olength (arrow [(olist _X)] nat). 

known_false (app eq [onil, (app ocons [X, Y])]) _.
known_false (app eq [(app ocons [X, Y]), onil]) _.
known_false (app eq [zero, (app s [X])]) _.
known_false (app eq [(app s [X]), zero]) _.

lemma pdd_nominate_tests cons_functional equiv trueP 
(app eq [(app ocons [X, Y]), (app ocons [W, Z])]) 
(app and [(app eq [X, W]), (app eq [Y, Z])]).

definition pdd_nominate_tests oapp1 trueP 
	   (app oapp [onil, Y]) 
	   Y. 
definition pdd_nominate_tests oapp2 trueP 
	   (app oapp [(app ocons [X, Y]), Z]) 
	   (app ocons [X, (app oapp [Z, Y])]).

definition pdd_nominate_tests olength1 trueP 
	   (app olength [onil]) 
	   zero.
definition pdd_nominate_tests olength2 trueP 
	   (app olength [(app ocons [_H, T])]) 
	   (app s [(app olength [T])]).


definition pdd_nominate_tests omem1 trueP 
	   (app omember  [_X,  onil]) 
	   falseP.
definition pdd_nominate_tests omem2 (app neq  [X, Y])
    (app omember  [X, (app ocons  [Y, Z])])
    (app omember  [X, Z]).
definition pdd_nominate_tests omem3 trueP
    (app omember  [X, (app ocons  [X, Z])])
    (trueP).

definition pdd_nominate_tests sort1
	trueP
	(app sort [onil])
	onil.
definition pdd_nominate_tests sort2
	trueP
	(app sort [(app ocons [H, T])])
	(app insert [H, (app sort [T])]).

definition pdd_nominate_tests insert1
	trueP
	(app insert  [N, onil])
	(app ocons  [N, onil]).
definition pdd_nominate_tests insert2
	(app less  [N, H])
	(app insert  [N, (app ocons  [H, T])])
	(app ocons  [N, (app ocons  [H, T])]).
definition pdd_nominate_tests insert3
	(app neg [(app less  [N, H])])
	(app insert  [N, (app ocons  [H, T])])
	(app ocons  [H, (app insert  [N, T])]).

definition pdd_nominate_tests count1
	trueP
	(app count  [A, onil])
	zero.
definition pdd_nominate_tests count2
	(app eq  [A, H])
	(app count  [A, (app ocons  [H, T])])
	(app s [(app count  [A, T])]).
definition pdd_nominate_tests count3
	(app neq  [A, H])
	(app count  [A, (app ocons  [H, T])])
	(app count  [A, T]).

definition pdd_nominate_tests ordered1
	trueP
	(app ordered [onil])
	trueP.
definition pdd_nominate_tests ordered2
	trueP
	(app ordered [(app ocons  [X, onil])])
	trueP.
definition pdd_nominate_tests ordered3
	(app less  [Y, X])
	(app ordered [(app ocons  [X, (app ocons  [Y, T])])])
	falseP.
definition pdd_nominate_tests ordered4
	(app neg [(app less  [Y, X])])
	(app ordered [(app ocons  [X, (app ocons  [Y, T])])])
	(app ordered [(app ocons [Y, T])]).

% Two step list induction
%
induction_scheme  pdd_nominate_tests list_twostep
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
induction_scheme  pdd_nominate_tests list_struct
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




% simple list theory
% 
top_goal_c pdd_nominate_tests assapp []
     (app and [(app forall [(olist nat), 
          (abs (x\ (app forall [(olist nat),  
          (abs (y\ (app forall [(olist nat), 
          (abs (z\ (app eq [(app oapp [(app oapp [x, y]),  z]),  
                            (app oapp [x, (app oapp [y, z])])])) 
          (olist nat))])) (olist nat))])) (olist nat))]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].



top_goal_c pdd_nominate_tests app1right []
	(app and [(app forall  [(olist nat), (abs (v0\ 
		(app eq  [(app oapp  [v0, onil]),
				 v0])) (olist nat))]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests cnc_app []
	(app and [(app forall  [(olist nat), (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app eq  [v1, v2]),
			(app eq  [(app oapp  [v0, v1]),
					(app oapp  [v0, v2])])])) (olist nat))])) (olist nat))])) (olist nat))]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests cnc_cons []
	(app and [(app forall  [nat, (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app eq  [v1, v2]),
			 (app eq  [(app ocons  [v0, v1]),
					 (app ocons  [v0, v2])])])) (olist nat))])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].


top_goal_c pdd_nominate_tests cnc_cons2 []
	(app and [(app forall  [nat, (abs (v0\ 
		(app forall  [nat, (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app eq  [v0, v1]),
			(app eq  [(app ocons  [v0, v2]),
					(app ocons  [v1, v2])])])) (olist nat))])) nat)])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests comapp []
	(app and [(app forall  [(olist nat), (abs  (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
	(app eq  [(app olength [(app oapp  [v0, v1])]), 
			(app olength [(app oapp  [v1, v0])])])) (olist nat))])) (olist nat))]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests memapp2 []
	(app and [(app forall  [nat, (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app omember  [v0, v2]),
			 (app omember  [v0, (app oapp  [v1, v2])])])) (olist nat))])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests memapp3 []
	(app and [(app forall  [nat, (abs (v0\ 
		(app forall  [(olist nat), (abs (v1\ 
			(app forall  [(olist nat), (abs (v2\ 
	(app imp  [(app or  [(app omember  [v0, v1]),
					 (app omember  [v0, v2])]),
			 (app omember  [v0, (app oapp  [v1, v2])])])) (olist nat))])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].



top_goal_c pdd_nominate_tests memapp []
        (app and [(app forall  [nat, (abs (a\
                (app forall  [(olist nat), (abs (t\
                        (app forall  [(olist nat), (abs (l\
        (app imp  [(app omember  [a, t]), 
                         (app omember  [a, (app oapp  [t, l])])])) (olist nat))])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests countsort []
	(app and [(app forall  [nat, (abs (a\
		(app forall  [(olist nat), (abs (l\
	(app eq  [(app count  [a, (app sort [l])]),
			(app count  [a, l])])) (olist nat))])) nat)]), diagnose])

	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)]),
	   (banned [memins1, memins2])].

top_goal_c pdd_nominate_tests lensort []
	(app and [(app forall  [(olist nat), (abs (l\
		(app eq  [(app olength [(app sort [l])]), (app olength [l])])) (olist nat))]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)]),
	   (banned [memins1, memins2])].

top_goal_c pdd_nominate_tests memins []
	(app and [(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app omember  [x, (app insert  [x, y])])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)]),
	   (banned [memins1, memins2])].

top_goal_c pdd_nominate_tests meminsert1 []
	(app and [(app forall  [nat, (abs (a\
		(app forall  [nat, (abs (b\
			(app forall  [(olist nat), (abs (l\
	(app imp  [(app eq  [a, b]),
		(app omember  [a, (app insert  [b, l])])])) (olist nat))])) nat)])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)]),
	   (banned [memins1, memins2])].

top_goal_c pdd_nominate_tests meminsert2 []
        (app and [(app forall  [nat, (abs (a\
                (app forall  [nat, (abs (b\
                        (app forall  [(olist nat), (abs (l\
        (app imp  [(app neq  [a, b]),
                (app eq  [
                        (app omember  [a, (app insert  [b, l])]),
                        (app omember  [a, l])])])) (olist nat))])) nat)])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)]),
	   (banned [memins1, memins2])].

lemma pdd_nominate_tests memins1 rtol
      trueP
      (app omember [X, (app insert [X, L])])
      trueP.
lemma pdd_nominate_tests memins2 rtol
      (app neq [A, B])
      (app omember [A, (app insert [B, L])])
      (app omember [A, L]).

top_goal_c pdd_nominate_tests memsort1 []
	(app and [(app forall  [nat, (abs (x\
	(app forall  [(olist nat), (abs (l\
		(app imp  [(app omember  [x, (app sort [l])]),
			 (app omember  [x, l])])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests memsort2 []
	(app and [(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (l\
			(app imp  [(app omember  [x, l]),
					(app omember  [x, (app sort [l])])])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)])].

top_goal_c pdd_nominate_tests ordered_cons []
	(app and [(app forall  [nat, (abs (x\
		(app forall  [(olist nat), (abs (y\
	(app imp  [
		(app ordered [(app ocons  [x, y])]),
		(app ordered [y])])) (olist nat))])) nat)]), diagnose])
	  [(unsure oapp [(rrstatus oapp1 Tree1 [] Used1),
			 (rrstatus oapp2 Tree2 [] Used2)]),
	   (unsure omember [(rrstatus omem1 Tree4 [] Used4),
			    (rrstatus omem2 Tree5 [] Used5),
			    (rrstatus omem3 Tree6 [] Used6),
                            (rrstatus memins1 Tree7 [] Used7),
                            (rrstatus memins2 Tree8 [] Used8)]),
	   (unsure insert [(rrstatus insert1 Tree9 [] Used9),
			    (rrstatus insert2 Tree10 [] Used10),
			    (rrstatus insert3 Tree11 [] Used11)]),
	   (unsure count  [(rrstatus count1 Tree12 [] Used12),
			    (rrstatus count2 Tree13 [] Used13),
			    (rrstatus count3 Tree14 [] Used14)]),
	   (unsure sort [(rrstatus sort1 Tree15 [] Used15),
			 (rrstatus sort2 Tree16 [] Used16)]),
	   (banned [memins1, memins2])].

benchmark_plan pdd_nominate_tests Meth Query :-
        testloop (%interaction_mode command,
        (set_theory_induction_scheme_list arithmetic,
        (add_theory_to_induction_scheme_list pdd_nominate_tests,
        (set_sym_eval_list [idty, s_functional, cons_functional, mono_fun_1, mono_fun_2, neq_zero_s, neq_s_zero, memins1, memins2, and1, and2, and3, and4, neq_eq, imp1, imp2, imp3],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (add_theory_defs_to_sym_eval_list pdd_nominate_tests,
        (set_wave_rule_to_sym_eval,
        pds_plan Meth Query
	))))))).

%% Compilation aid

end





