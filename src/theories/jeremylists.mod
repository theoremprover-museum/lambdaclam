/*

File: jeremylists.mod
Author: Louise Dennis
Description:  Definitions I think related to Jeremy's work.  Untested using file largely to store the code for future consideration and so clean up objlists which was getting confused.
Last Modified: 6th March 2001

*/

module jeremylists.

accumulate jeremyarith.

definition objlists car2 trueP (app ocar (app ocons (tuple [X, _Y]))) X.
definition objlists car1 trueP (app ocar onil) undef.
definition objlists cdr2 trueP (app ocdr (app ocons (tuple [_X, Y]))) Y.
definition objlists cdr1 trueP (app ocdr onil) undef.

% drop
%
% (drop zero L) => L.
definition objlists drop1  trueP 
(app drop (tuple [zero, L]))
L.
%
% (drop N onil) => onil.
definition objlists drop2 trueP 
(app drop (tuple [_N, onil]))
onil.
%
% (drop (s X) (ocons H T)) => (drop X T).
definition objlists drop3 trueP 
(app drop (tuple [(app s X), (app ocons (tuple [_H, T]))]))
(app drop (tuple [X, T])).


% take
%
% (take zero L) => onil.
definition objlists take1 trueP 
(app take (tuple [zero, _]))
onil.
%
% (take N onil) => onil.
definition objlists take2 trueP 
(app take (tuple [_N, onil]))
onil.
%
% (take (s X) (ocons H T)) => (ocons H (take X T).
definition objlists take3 trueP 
(app take (tuple [(app s X), (app ocons (tuple [H, T]))]))
(app ocons (tuple [H, (app take (tuple [X, T]))])).

/*
% map 
%
definition objlists map1 trueP 
(app map (tuple [_, onil]))
onil.

definition objlists map2 trueP 
(app map (tuple [F, (app ocons (tuple [H, T]))]))
(app ocons (tuple [(app F H),
                 (app map (tuple [F, T]))])).


% foldL
%
definition objlists foldL1 trueP 
(app foldL (tuple [_, A, onil]))
A.

definition objlists foldL2 trueP 
(app foldL (tuple [F, A, (app ocons (tuple [H, T]))]))
(app foldL (tuple [F, (app F (tuple [A, H])), T])).

lemma objlists foldL_appel_lemma equiv trueP 
(app foldL (tuple [F, A, (app oapp (tuple [L, (app ocons (tuple [E, onil]))]))]))
(app F (tuple [(app foldL (tuple [F, A, L])), E])).


% foldR
%
definition objlists foldR1 trueP 
(app foldR (tuple [_, A, onil]))
A.

definition objlists foldR2 trueP 
(app foldR (tuple [F, A, (app ocons (tuple [H, T]))]))
(app F (tuple [H, (app foldR (tuple [F, A, T]))])).



% harald_opp_one and harald_opp_two
%
lemma objlists harald_lem_id equiv trueP 
(app harald_opp_one (tuple [harald_id, X]))
(app harald_opp_two (tuple [X, harald_id])).

lemma objlists harald_lem_ass equiv trueP 
(app harald_opp_one (tuple [(app harald_opp_two (tuple [X, Y])), Z]))
(app harald_opp_two (tuple [X, (app harald_opp_one (tuple [Y, Z]))])).

% paulson_opp
%
lemma objlists paulson_lem_id equiv trueP 
(app paulson_opp (tuple [X, paulson_id]))
X.

lemma objlists paulson_lem_ass equiv trueP 
(app paulson_opp (tuple [(app paulson_opp (tuple [X, Y])), Z]))
(app paulson_opp (tuple [X, (app paulson_opp (tuple [Y, Z]))])).




% dapp_cons
%
lemma objlists dapp_cons equiv trueP 
(app dapp (tuple [(app ocons (tuple [H, T])), L]))
(app ocons (tuple [H, (app dapp (tuple [T, L]))])).

lemma objlists dlen_cons equiv trueP 
(app dlen (app ocons (tuple [_, T])))
(app s (app dlen T)).


% dapp
%
% (dapp onil M) => M.
definition objlists dapp1 
trueP
(app dapp (tuple [onil, M]))
M.
% (neq L onil) -> (dapp L M) => (ocons (ocar L) (dapp (ocdr L) M)).
definition objlists dapp2 
(app neg (app eq (tuple [L, onil])))
(app dapp (tuple [L, M]))
(app ocons (tuple [(app ocar L), (app dapp (tuple [(app ocdr L), M]))])).

% dlen
%
% (dlen onil) => zero.
definition objlists dlen1 
trueP
(app dlen onil)
zero.
% (neq L onil) -> (dlen L) => (s (dlen (ocdr L))).
definition objlists dlen2 
(app neg (app eq (tuple [L, onil])))
(app dlen L)
(app s (app dlen (app ocdr L))).

% bin_dc
%
definition objlists bin_dc1 
trueP
(app bin_dc (tuple [_, B, onil]))
B.

definition objlists bin_dc2
trueP
(app bin_dc (tuple [_, _, (app ocons (tuple [X, onil]))]))
X.

definition objlists bin_dc3
(app and (tuple [(app neg (app eq (tuple [L, onil]))),
               (app neg (app eq (tuple [L, (app ocons (tuple [(app ocar L), onil]))])))]))
(app bin_dc (tuple [F, B, L]))
(app F (tuple [(app bin_dc (tuple [F, B,
                               (app take (tuple [(app div (tuple [(app olength L),
                                                   (app s (app s zero))])),
                                               L]))])),
             (app bin_dc (tuple [F, B,
                         (app drop (tuple [(app div (tuple [(app olength L),
                                                    (app s (app s zero))])),
                                               L]))]))])).


% split
%
definition objlists split1
trueP
(app split (tuple [zero, L]))
(app ocons (tuple [L, onil])).

definition objlists split2
trueP
(app split (tuple [(app s zero), L]))
(app ocons (tuple [L, onil])).

definition objlists split3
trueP
(app split (tuple [(app s (app s X)), L]))
(app ocons (tuple [(app take (tuple [(app div (tuple [(app olength L),
                                                 (app s (app s X))])),
                                 L])),
                 (app split (tuple [(app s X),
                        (app drop (tuple [(app div (tuple [(app olength L),
                                                      (app s (app s X))])),
                                                  L]))]))])).

*/

/*                             
%%
%% Non-constructor Style Schemes
%%

% Induction for Harald's problem
%
induction_scheme objlists harald_ind
   (olist T)
   empty
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [(olist T), (abs Prop)]))))
   % Base cases
   ( ( (seqGoal (H >>> (Prop onil))) **
           (allGoal T x\ (seqGoal (H >>> (Prop (app ocons (tuple [x, onil]))))))) **
   % Step case
   (allGoal T x\ (allGoal T h\ (allGoal (olist T) t\ (seqGoal (((otype_of x T)::
                                                  (otype_of h T)::
                                                  (otype_of t (olist T))::
                                                  (Prop t)::
					          (Prop (app ocons (tuple [h, t])))::
					          (Prop (app oapp (tuple [t, (app ocons (tuple [x, onil]))])))::H)
					         >>>
						 (Prop (app oapp (tuple [(app ocons (tuple [h, t])), (app ocons (tuple [x, onil]))]))))))))).

% Induction for Paulson's problem
%
induction_scheme objlists paulson_ind
   (olist T)
   empty
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [(olist T), (abs Prop)]))))
   % Base case
   ((seqGoal (H >>> (Prop onil)))
   % Step case
    **
    (allGoal T x\ (allGoal (olist T) l\ (seqGoal (((otype_of x T)::
                                                  (otype_of l (olist T))::
                                                  (Prop l)::H)
					         >>>
	 (Prop (app oapp (tuple [l, (app ocons (tuple [x, onil]))])))))))).


induction_scheme objlists bin_dc_ind
   (olist T)
   empty
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [(olist T), (abs Prop)]))))
   % Base cases
   (( (seqGoal (H >>> (Prop onil))) **
       (allGoal T x\ (seqGoal (((otype_of x T)::H) >>> (Prop (app ocons (tuple [x, onil])))))))
   % Step case
    **
    (allGoal (olist T) l\ (seqGoal (((otype_of l (olist T))::
                                     (app and (tuple [(app neg (app eq (tuple [l, onil]))),
                                                    (app neg (app eq (tuple [l, (app ocons (tuple [(app ocar l), onil]))])))]))::
                                     (Prop (app take (tuple [(N l), l])))::
                                     (Prop (app drop (tuple [(N l), l])))::H)
				 >>>
	 (Prop l))))) :- N = (u\ (app div (tuple [(app olength u), (app s (app s zero))]))).



% Dual induction to rotate
%
induction_scheme objlists rotate_ind
   % Info
   (tuple_type [nat, (olist T)])
   empty
   (measured nat n\ (measured (olist T) (Prop n)))
   % Goal
   (seqGoal (H >>> (app forall (tuple [nat,
                        (abs n\ (app forall (tuple [(olist T),
                                     (abs (Prop n))])))]))))
   % Base case
   ( (seqGoal (H >>> (app forall (tuple [(olist T), (abs (Prop zero))]))) **
   % Step case
   (allGoal nat x\ (allGoal T h\ (allGoal (olist T)
        (t\ (seqGoal (((otype_of x nat)::
                      (otype_of h T)::
                      (otype_of t (olist T))::
                      ((Prop x) (app oapp (tuple [t, (app ocons (tuple [h, onil]))])))::H)
                     >>>
                     ((Prop (app s x)) (app ocons (tuple [h, t]))))))))))).


% Two-variable cdr destructor style induction
%
induction_scheme objlists list_dest_twovar
   % Info
   (tuple_type [(olist T), (olist T2)])
   empty
   (measured (olist T) x\ (measured (olist T2) (Prop x)))
   % Goal
   (seqGoal (H >>> (app forall (tuple [(olist T), (abs x\ (app forall (tuple [(olist T2), (abs (Prop x))])))]))))
   % Base cases
   ( ( (allGoal (olist T) x\ (seqGoal (H >>> ((Prop x) onil))))  **
           (allGoal (olist T2) x\ (seqGoal (H >>> ((Prop onil) x))))) **
   % Step case
   (allGoal (olist T) (t\ (allGoal T2
       (t2\ (seqGoal (((otype_of t (olist T))::
                       (otype_of t2 (olist T2))::
                       (app neg (app eq (tuple [t, onil])))::
		       (app neg (app eq (tuple [t2, onil])))::
		       ((Prop (app ocdr t)) (app ocdr t2))::H)
                     >>>
                     ((Prop t) t2)))))))).

% Destructor style structural induction for lists
%
induction_scheme objlists list_dest_struct
   % Info
   (olist T)
   empty
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [(olist T), (abs Prop)]))))
   % Base case
   ((seqGoal (H >>> (Prop onil)))
   % Step case
    **
    (allGoal (olist T)
        (t\ (seqGoal (((otype_of t (olist T))::(app neg (app eq (tuple [t, onil])))::(Prop (app ocdr t))::H)
                     >>>
                     (Prop t)))))).


%%
%% Constructor Style Schemes
%% 

% Dual induction to drop and take
%
induction_scheme objlists s_cons_ind
   % Info
   (tuple_type [nat, (olist T)])
   empty
   (measured nat n\ (measured (olist T) (Prop n)))
   % Goal
   (seqGoal (H >>> (app forall (tuple [nat,
           (abs n\ (app forall (tuple [(olist T), (abs (Prop n))])))]))))
   % Base case
   ((seqGoal (H >>> (app forall (tuple [nat, (abs n\ ((Prop n) onil))]))) **
   % Step case
   (allGoal nat x\ (allGoal T h\ (allGoal (olist T)
        (t\ (seqGoal (((otype_of x nat)::
                      (otype_of h T)::
                      (otype_of t (olist T))::
                      ((Prop x) t)::H)
                     >>>
                     ((Prop (app s x)) (app ocons (tuple [h, t]))))))))))).

% `cons to double cons' list induction.
%
induction_scheme  objlists c_to_cc_ind
  % Info
  (olist T)
  (dom (a \ 
   (dom (b \ 
    (dom (c \ 
     (repl (app ocons (tuple [b, c])) 
           (app ocons (tuple [a, (app ocons (tuple [b, c]))])))))))))
  (measured (olist T) Prop)
  % Goal
  ( seqGoal (H >>> (app forall (tuple [(olist T), (abs Prop)] ) )))
  % Base case 1
  ( ((seqGoal (H >>> (Prop onil ))) **
  % Base case 2
              (allGoal T s\ 
                (seqGoal (((otype_of s T)::H)
                     >>> (Prop (app ocons (tuple [s, onil] ))))))) **
  % Step case
  (allGoal (olist T) (t\ (allGoal T (h\ 
    (allGoal T (i\ 
     (seqGoal (((otype_of h T)::
                (otype_of i T)::
                (otype_of t (olist T))::
                (Prop (app ocons (tuple [i, t])))::H)
            >>> (Prop (app ocons (tuple [h, (app ocons (tuple [i, t]))]))))))) ))
                   ))).

*/

/*  
%
% Dual inductions for list functions.
%
list_dual olength (measured (olist _) l\ (app olength l))                     list_strucnt.
list_dual orev    (measured (olist _) l\ (app orev l))                        list_struct.

list_dual oapp    (measured (olist T) l\ (free (olist T) m\ (app oapp (pair l m))))         list_struct.
list_dual omember (measured (olist T) l\ (free T x\ (app omember (pair x l))))              list_struct.
list_dual qrev    (measured (olist T) l\ (free (olist T) m\ (app qrev (pair l m))))         list_struct.
list_dual allList (measured (olist T) l\ (free (T arrow bool) p\ (app allList (pair p l)))) list_struct.
list_dual map     (measured (olist B) l\ (free (_ arrow B) f\ (app map (pair f l))))        list_struct.

list_dual dapp    (measured (olist T) l\ (free (olist T) m\ (app dapp (pair l m))))  list_dest_struct.
list_dual dlen    (measured (olist _) l\ (app dlen l))                                list_dest_struct.

list_dual drop (measured nat n\ (measured (olist _) l\ (app drop (pair n l))))    s_cons_ind.
list_dual take (measured nat n\ (measured (olist _) l\ (app take (pair n l))))    s_cons_ind.
list_dual rotate (measured nat n\ (measured (olist _) l\ (app rotate (pair n l))))  rotate_ind.

list_dual foldL (measured (olist B) l\ (free ((tuple_type [A, B]) arrow A) f\ (free A a\ (app foldL (pair f (pair a l)))))) list_struct.
list_dual foldR (measured (olist B) l\ (free ((pair_type B A) arrow A) f\ (free A a\ (app foldR (pair f (pair a l)))))) list_struct.

%list_dual foldR (measured (olist anytype) l\ (free ((pair_type anytype anytype) arrow anytype) f\ (free anytype a\ (app foldR (pair f (pair a l)))))) harald_ind.
%list_dual foldL (measured (olist anytype) l\ (free ((pair_type anytype anytype) arrow anytype) f\ (free anytype a\ (app foldL (pair f (pair a l)))))) paulson_ind.

list_dual bin_dc (measured (olist T) l\ (free ((pair_type T T) arrow T) f\ (free T b\ (app bin_dc (pair f (pair b l)))))) bin_dc_ind.
list_dual split  (measured nat n\ (free (olist _) l\ (app split (pair n l)))) s_to_ss_ind.

*/


/*
% Harald's problem
%
% Proved by CP with foldL_appel_lemma
%
top_goal objlists haralds_problem []
(app forall (tuple [(olist anytype),
(abs l\ (app eq (tuple [(app foldL (tuple [harald_opp_one, harald_id, l])),
                      (app foldR (tuple [harald_opp_two, harald_id, l]))])))])).

top_goal objlists haralds_problem2 []
(app forall (tuple [(universe arrow bool), (abs t\ (app forall (tuple [(olist t),
(abs l\ (app eq (tuple [(app foldL (tuple [harald_opp_one, harald_id, l])),
                      (app foldR (tuple [harald_opp_two, harald_id, l]))])))])))])).



% Paulson's problem
%
% Proved by CP with foldL_appel_lemma
%
top_goal objlists paulsons_problem []
(app forall (tuple [(anytype arrow bool), (abs a\ (app forall (tuple [(olist anytype), (abs l\ (app eq (tuple [(app paulson_opp (tuple [a, (app foldL (tuple [paulson_opp, paulson_id, l]))])), (app foldL (tuple [paulson_opp, a, l]))])))])))])).


top_goal objlists paulsons_problem2 []
(app  forall (tuple [universe, (abs t\ (app forall (tuple [t, (abs a\ (app forall (tuple [(olist t), (abs l\ (app eq (tuple [(app paulson_opp (tuple [a, (app foldL (tuple [paulson_opp, paulson_id, l]))])), (app foldL (tuple [paulson_opp, a, l]))])))])))])))])).


% Divide and Conquer
%
top_goal objlists divide_and_conquer []
(app forall (tuple [universe,
(abs t\ (app forall (tuple [(tuple_type [t, t]) arrow t,
(abs f\ (app forall (tuple [t,
(abs b\ (app forall (tuple [t,
(abs x\ (app forall (tuple [(olist t),
(abs l\ (app forall (tuple [nat,
(abs n\ (app imp (tuple [
(app eq (tuple [(app f (tuple [b, x])), x])),
(app eq (tuple [(app bin_dc (tuple [f, b, l])),
              (app foldR (tuple [f, b,
                         (app foldR (tuple [oapp, onil,
   (app map (tuple [(abs v\ (app map (tuple [(abs u\ (app f (tuple [b, u]))),
   v]))),
         (app split (tuple [n, l]))]))]))]))]))])))])))])))])))])))])))])).
                                                              

%
% foldL_appel
% Used as a lemma above.
%
top_goal objlists foldL_appel []
(app forall (tuple [(tuple_type [anytype, anytype]) arrow anytype,
	(abs f\ (app forall (tuple [anytype, 
		(abs a\ (app forall (tuple [anytype,
			(abs e\ (app forall (tuple [(olist anytype),
   (abs l\ (app eq (tuple [(app foldL (tuple [f, (tuple [a, (app oapp (tuple [l, (app ocons (tuple [e, onil]))]))])])),
	 (app f (tuple [(app foldL (tuple [f, a, l])), e]))])))])))])))])))])).

top_goal objlists foldL_appel2 []
(app forall (tuple [(universe arrow bool),
	(abs t\ (app forall (tuple [(tuple_type [t, t]) arrow t,
		(abs f\ (app forall (tuple [t,
			(abs a\ (app forall (tuple [t,
				(abs e\ (app forall (tuple [(olist t),
    (abs l\ (app eq (tuple [(app foldL (tuple [f, a, (app oapp (tuple [l, (app ocons (tuple [e, onil]))]))])), (app f (tuple [(app foldL (tuple [f, a, l])), e]))])))])))])))])))])))])).
*/


end