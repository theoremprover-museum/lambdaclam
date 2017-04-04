/*

File: ccs_hmf_methods.mod
Author: James Brotherston
Description: Methods and rewrite rules for modal properties of CCS processes
Last Modified: 26th July 2002

*/

module ccs_hmf_methods.

accumulate ccs_hmf_syntax.

%% Definition of transitional behaviour of CCS processes

ccs_transition (app dot (tuple [A,F])) A F.
ccs_transition (app ccs_plus (tuple [E1,E2])) A F:-
   (ccs_transition E1 A F ; ccs_transition E2 A F).
ccs_transition (app bar (tuple [E1,E2])) A (app bar (tuple [F,E2])):- 
   ccs_transition E1 A F.
ccs_transition (app bar (tuple [E1,E2])) A (app bar (tuple [E1,F])):-
   ccs_transition E2 A F.
ccs_transition (app bar (tuple [E1,E2])) tau (app bar (tuple [F1,F2])):-
   ((ccs_transition E1 A F1, ccs_transition E2 (app co A) F2) ; 
    (ccs_transition E2 A F2, ccs_transition E1 (app co A) F1)).
ccs_transition (app slash (tuple [E,J])) A (app slash (tuple [F,J])):-
   ccs_transition E A F, ccs_slash_condition A J.
ccs_transition E A F:-
   definition ccs_hmf_theory _DefName trueP E E', 
   ccs_transition E' A F, 
   print "Expanding definition: ", printstdout E, 
   print " = ", pprint_term E', !.


local ccs_slash_condition osyn -> osyn -> o.

ccs_slash_condition A onil.
ccs_slash_condition A (app ocons (tuple [J, RestJ])):-
   (not (A = J)), (not (A = (app co J))), ccs_slash_condition A RestJ.


%% Size measure on formulas of M (currently unused)

hmf_size tt 0.
hmf_size ff 0.
hmf_size (app and (tuple [M1,M2])) (S1+S2+1):-
   hmf_size M1 S1, hmf_size M2 S2.
hmf_size (app or (tuple [M1,M2])) (S1+S2+1):-
   hmf_size M1 S1, hmf_size M2 S2.
hmf_size (app box (tuple [K,M])) (S+1):- hmf_size M S.
hmf_size (app diamond (tuple [K,M])) (S+1):- hmf_size M S.


%% Definition of complementation on modal formulas

definition ccs_hmf_methods tt_comp trueP
   (app hmf_comp tt) ff.

definition ccs_hmf_methods ff_comp trueP
   (app hmf_comp ff) tt.

definition ccs_hmf_methods and_comp trueP
   (app hmf_comp (app and (tuple [A,B])))
   (app or (tuple [(app hmf_comp A),(app hmf_comp B)])).

definition ccs_hmf_methods or_comp trueP
   (app hmf_comp (app or (tuple [A,B])))
   (app and (tuple [(app hmf_comp A),(app hmf_comp B)])).

definition ccs_hmf_methods box_comp trueP
   (app hmf_comp (app box (tuple [K,Phi])))
   (app diamond (tuple [K,(app hmf_comp Phi)])).

definition ccs_hmf_methods diamond_comp trueP
   (app hmf_comp (app diamond (tuple [K,Phi])))
   (app box (tuple [K,(app hmf_comp Phi)])).


%% Methods for satisfaction of modal formulas

atomic ccs_hmf_methods sat_true
   (seqGoal (_H >>> (app satisfies (tuple [_E, tt]))))
   true
   true
   trueGoal
   notacticyet.

atomic ccs_hmf_methods sat_and_i
   (seqGoal (H >>> (app satisfies (tuple [E, (app and (tuple[M,N]))]))))
   true
   true
   ((seqGoal (H >>> (app satisfies (tuple [E,M])))) **
    (seqGoal (H >>> (app satisfies (tuple [E,N])))))
   notacticyet.

atomic ccs_hmf_methods sat_and_e
   (seqGoal (H >>> G))
   (memb (app satisfies (tuple [E,(app and (tuple [A,B]))])) H,
    replace_in_hyps H (app satisfies (tuple [E,(app and (tuple [A,B]))])) 
    ((app satisfies (tuple [E,A]))::(app satisfies (tuple [E,B]))::nil) H1)
   true
   (seqGoal (H1 >>> G))
   notacticyet.

atomic ccs_hmf_methods sat_or_e
   (seqGoal (H >>> G))
   (memb (app satisfies (tuple [E,(app or (tuple [A,B]))])) H,
    replace_in_hyps H (app satisfies (tuple [E,(app or (tuple [A,B]))])) 
    ((app satisfies (tuple [E,A]))::nil) H1,
    replace_in_hyps H (app satisfies (tuple [E,(app or (tuple [A,B]))])) 
    ((app satisfies (tuple [E,B]))::nil) H2)
   true
   ((seqGoal (H1 >>> G))**(seqGoal (H2 >>> G)))
   notacticyet.

atomic ccs_hmf_methods sat_or_i1
   (seqGoal (H >>> (app satisfies (tuple [E, (app or (tuple[M,N]))]))))
   true
   true
   (seqGoal (H >>> (app satisfies (tuple [E,M]))))
   notacticyet.

atomic ccs_hmf_methods sat_or_i2
   (seqGoal (H >>> (app satisfies (tuple [E, (app or (tuple[M,N]))]))))
   true
   true
   (seqGoal (H >>> (app satisfies (tuple [E,N]))))
   notacticyet.


%% Methods and auxiliaries dealing with modal operators 

atomic ccs_hmf_methods sat_box
   (seqGoal (H >>> (app satisfies (tuple [E, (app box (tuple [K, M]))]))))
   (find_transitions E K Fs, 
    mk_box_goals H Fs M OutputGoal)
   true
   OutputGoal
   notacticyet.

atomic ccs_hmf_methods sat_diamond
   (seqGoal (H >>> (app satisfies (tuple [E, (app diamond (tuple [K, M]))]))))
   (find_transitions E K Fs, !,
    mk_diamond_goals H Fs M OutputGoal)
   true
   OutputGoal
   notacticyet.

local find_transitions osyn -> osyn -> (list osyn) -> o.
local find_all_transitions osyn -> osyn -> (list osyn) -> o.
local find_minus_transitions osyn -> osyn -> (list osyn) -> o.
local convert_action_list osyn -> (list osyn) -> o.
local mk_box_goals (list osyn) -> (list osyn) -> osyn -> goal -> o.
local mk_diamond_goals (list osyn) -> (list osyn) -> osyn -> goal -> o.
local mk_diamond_disj (list osyn) -> osyn -> osyn -> o.

find_transitions E onil [].
find_transitions E ActionList Fs:-
   ActionList = (app ocons (tuple [A,As])),
   ((A = allminus, find_minus_transitions E As Fs) ;
    ((not (A = allminus)), find_all_transitions E ActionList Fs)).

find_all_transitions E onil [].
find_all_transitions E (app ocons (tuple [A, As])) Fs:-
   findall (F\ (ccs_transition E A F)) FirstFs,
   find_all_transitions E As RestFs,
   append FirstFs RestFs Fs.

find_minus_transitions E As Fs:- 
   convert_action_list As ListAs,
   pprint_string "Ignoring transitions for actions:",
   pprint_action_list ListAs,
   findall (F\ ((sigma A\ 
      (ccs_transition E A F), (not (member A ListAs))))) Fs.

convert_action_list onil [].
convert_action_list (app ocons (tuple [A,As])) (A::RestAs):-
   convert_action_list As RestAs.

local pprint_action_list (list osyn) -> o.
pprint_action_list [].
pprint_action_list (A::As):- pprint_term A, pprint_action_list As.

mk_box_goals H [F] M (seqGoal (H >>> (app satisfies (tuple [F,M])))):- !.
mk_box_goals H [] M trueGoal:- 
   pprint_string "Process has no appropriate transition!".
mk_box_goals H (F::Fs) M Goal:-
   mk_box_goals H Fs M RestGoal, 
   Goal = ((seqGoal (H >>> (app satisfies (tuple [F,M])))) ** RestGoal).

mk_diamond_goals H [] M falseGoal:- 
   pprint_string "Process has no transitions!", fail.
mk_diamond_goals H Fs M Goal:-
   mk_diamond_disj Fs M Disj,
   Goal = (seqGoal (H >>> Disj)).

mk_diamond_disj [F] M (app satisfies (tuple [F,M])).
mk_diamond_disj (F::Fs) M (app or (tuple [(app satisfies (tuple[F,M])), D])):-
   mk_diamond_disj Fs M D.

%% Definition of exponentiation on box and diamond

definition ccs_hmf_methods exp_box_base trueP 
   (app exp_box (tuple [A,zero,F]))
   F.

definition ccs_hmf_methods exp_box_step trueP
   (app exp_box (tuple [A,(app s N),F]))
   (app box (tuple [A, (app exp_box (tuple [A,N,F]))])).

definition ccs_hmf_methods exp_diamond_base trueP 
   (app exp_diamond (tuple [A,zero,F]))
   F.

definition ccs_hmf_methods exp_diamond_step trueP
   (app exp_diamond (tuple [A,(app s N),F]))
   (app diamond (tuple [A, (app exp_diamond (tuple [A,N,F]))])).

%% General method for proving satisfaction of modal formulas

compound ccs_hmf_methods sat_meth
   (repeat_meth
	 (orelse_meth all_i
         (orelse_meth sat_true
         (orelse_meth sat_and_i
	 (orelse_meth sat_and_e
	 (orelse_meth sat_or_e
         (orelse_meth sat_or_i1
         (orelse_meth sat_or_i2
         (orelse_meth sat_box sat_diamond)))))))))
   _
   true.

%% General method for proving satisfaction via induction on parameters

compound ccs_hmf_methods sat_ind_meth
   (complete_meth
    (then_meth sat_meth 
     (then_meth (repeat_meth all_e)
      (then_meth (try_meth (induction_meth normal_ind Sch Sub))
       (map_meth
        (repeat_meth
	 (orelse_meth trivial
         (orelse_meth (deploy_lemma L)
         (orelse_meth sat_meth
         (orelse_meth fertilise
         (orelse_meth (unfold_defn D) imp_i)
         ))))))))))
   _
   true.

%% Induction scheme for HM formulas

induction_scheme ccs_hmf_methods hmf_struct 
  hmf
  (dom (phi\ (dom (k\ (repl phi (app box (tuple [k,phi])))))))
  (measured hmf Prop)
  (seqGoal (H >>> (app forall (tuple [hmf, (abs Prop)]))))
  (Goal1 ** (Goal2 ** (Goal3 ** (Goal4 ** (Goal5 ** Goal6))))):-
    Goal1 = (seqGoal (H >>> (Prop tt))),
    Goal2 = (seqGoal (H >>> (Prop ff))),
    Goal3 = (allGoal hmf phi1\ (allGoal hmf phi2\
	      (seqGoal (((otype_of phi1 hmf)::(otype_of phi2 hmf)::(Prop phi1)::(Prop phi2)::H) >>> (Prop (app and (tuple [phi1,phi2]))))))),
    Goal4 = (allGoal hmf phi1\ (allGoal hmf phi2\
	      (seqGoal (((otype_of phi1 hmf)::(otype_of phi2 hmf)::(Prop phi1)::(Prop phi2)::H) >>> (Prop (app or (tuple [phi1,phi2]))))))),
    Goal5 = (allGoal hmf phi\ (allGoal (olist action) k\
	      (seqGoal (((otype_of phi hmf)::(otype_of k (olist action))::(Prop phi)::H) >>> (Prop (app box (tuple [k,phi]))))))),
    Goal6 = (allGoal hmf phi\ (allGoal (olist action) k\
	      (seqGoal (((otype_of phi hmf)::(otype_of k (olist action))::(Prop phi)::H) >>> (Prop (app diamond (tuple [k,phi]))))))).



%% General method for structural induction proofs on formulas

compound ccs_hmf_methods sat_struct_meth
   (complete_meth 
     (then_meth (try_meth (induction_meth normal_ind Sch Sub))
	(repeat_meth 
	  (orelse_meth (unfold_defn D) 
          (orelse_meth trivial 
	  (orelse_meth equality_condition fertilise))))))
   _
   true.

%% Logical methods; methods dealing with iff are strangely absent elsewhere

atomic ccs_hmf_methods iff_i
   (seqGoal (H >>> (app iff (tuple [A,B]))))
   true
   true
   ((seqGoal (H >>> (app imp (tuple [A,B])))) ** 
    (seqGoal (H >>> (app imp (tuple [B,A])))))
   notacticyet.

compound ccs_hmf_methods logic_simplify
   (repeat_meth
     (orelse_meth iff_i
     (orelse_meth false_e 
     (orelse_meth trivial 
     (orelse_meth imp_i imp_e1
     )))))
   _
   true.




end