/*

File: mlremovelists.mod
Author: Louise Dennis
Description:  Examples taken from an ML exercise.  Many incorrect.
Last Modfied: 11th December 2000

*/

module mlremovelists.

accumulate objlists.

%% Canonical
has_otype mlremovelists tremoveOne ((tuple_type [nat, (olist nat)]) arrow (olist nat)).
has_otype mlremovelists tremoveAll ((tuple_type [nat, (olist nat)]) arrow (olist nat)).
has_otype mlremovelists tonceOnly ((olist nat) arrow (olist nat)).

definition mlremovelists tremoveOne1
	trueP
	(app tremoveOne (tuple [N, onil]))
	onil.
definition mlremovelists tremoveOne2
	(app eq (tuple [N, H]))
	(app tremoveOne (tuple [N, (app ocons (tuple [H, T]))]))
	T.
definition mlremovelists tremoveOne3
	(app neq (tuple [N, H]))
	(app tremoveOne (tuple [N, (app ocons (tuple [H, T]))]))
	(app ocons (tuple [H, (app tremoveOne (tuple [N, T]))])).

definition mlremovelists tremoveAll1
	trueP
	(app tremoveAll (tuple [N, onil]))
	onil.
definition mlremovelists tremoveAll2
	(app eq (tuple [N, H]))
	(app tremoveAll (tuple [N, (app ocons (tuple [H, T]))]))
	(app tremoveAll (tuple [N, T])).
definition mlremovelists tremoveAll3
	(app neq (tuple [N, H]))
	(app tremoveAll (tuple [N, (app ocons (tuple [H, T]))]))
	(app ocons (tuple [H, (app tremoveAll (tuple [N, T]))])).

definition mlremovelists tonceOnly1
	trueP
	(app tonceOnly onil)
	onil.
definition mlremovelists tonceOnly2
	trueP
	(app tonceOnly (app ocons (tuple [H, T])))
	(app ocons (tuple [H, (app tonceOnly (app tremoveAll (tuple [H, T])))])).



%%%% Common alternative for onceOnly

has_otype mlremovelists tonceOnlya ((olist T) arrow (olist T)).

definition mlremovelists tonceOnlya1
	trueP
	(app tonceOnlya onil)
	onil.
definition mlremovelists tonceOnlya2
	trueP
	(app tonceOnlya (app ocons (tuple [H, T])))
	(app ocons (tuple [H, (app tremoveAll (tuple [H, (app tonceOnlya T)]))])).


%%%%%%%%%

% abuse of polarity
lemma mlremovelists rArA equiv
	trueP
	(app tremoveAll (tuple [H, (app tremoveAll (tuple [H, L]))]))
	(app tremoveAll (tuple [H, L])).


top_goal mlremovelists onceOnly_query
	[]
	(app forall (tuple [(olist A),
		(abs l\
			(app eq (tuple [
				(app tonceOnly l),
				(app tonceOnlya l)
				]
			))
		)
	])).


%%%%%%%%%%%%%%%%%%%

has_otype mlremovelists drop ((tuple_type [nat, (olist A)]) arrow (olist A)).
has_otype mlremovelists take ((tuple_type [nat, (olist A)]) arrow (olist A)).

% drop
%
% (drop zero L) => L.
definition mlremovelists drop1  trueP 
(app drop (tuple [zero, L]))
L.
%
% (drop N onil) => onil.
definition mlremovelists drop2 trueP 
(app drop (tuple [_N, onil]))
onil.
%
% (drop (s X) (ocons H T)) => (drop X T).
definition mlremovelists drop3 trueP 
(app drop (tuple [(app s X), (app ocons (tuple [_H, T]))]))
(app drop (tuple [X, T])).


% take
%
% (take zero L) => onil.
definition mlremovelists take1 trueP 
(app take (tuple [zero, _]))
onil.
%
% (take N onil) => onil.
definition mlremovelists take2 trueP 
(app take (tuple [_N, onil]))
onil.
%
% (take (s X) (ocons H T)) => (ocons H (take X T).
definition mlremovelists take3 trueP 
(app take (tuple [(app s X), (app ocons (tuple [H, T]))]))
(app ocons (tuple [H, (app take (tuple [X, T]))])).

has_otype mlremovelists filt ((tuple_type [(X arrow bool), (olist X)]) arrow (olist X)).
definition mlremovelists filt1
	trueP
	(app filt (tuple [P, onil]))
	onil.
definition mlremovelists filt2
	(app P H)
	(app filt (tuple [P, (app ocons (tuple [H, T]))]))
	(app ocons (tuple [H, (app filt (tuple [P, T]))])).
definition mlremovelists filt3
	(app neg (app P H))
	(app filt (tuple [P, (app ocons (tuple [H, T]))]))
	(app filt (tuple [P, T])).
%%%%%%%


%%%%%%%%%%  Sample Hypothetical Student Program  %%%%%%%%%%%%%
has_otype mlremovelists sremoveOne ((tuple_type [A, (olist A)]) arrow (olist A)).

definition mlremovelists sremoveOne1
	trueP
	(app sremoveOne (tuple [N, onil]))
	onil.
definition mlremovelists sremoveOne2
	(app eq (tuple [N, H]))
	(app sremoveOne (tuple [N, (app ocons (tuple [H, T]))]))
	T.
definition mlremovelists sremoveOne3
	(app neq (tuple [N, H]))
	(app sremoveOne (tuple [N, (app ocons (tuple [H, T]))]))
	(app ocons (tuple [H, (app sremoveOne (tuple [N, T]))])).


top_goal mlremovelists stsimple
	[]
	(app forall (tuple [(olist nat),
		(abs l\
	(app forall (tuple [nat,
		(abs n\
			(app eq (tuple [
				(app sremoveOne (tuple [n, l])),
				(app tremoveOne (tuple [n, l]))
				]
			))
		)
	])))])).

%%%%%%%%%%%%%%%

compound mlremovelists ml_meth (complete_meth
		(repeat_meth
		(orelse_meth trivial
		(orelse_meth allFi
	 	(orelse_meth taut
            	(orelse_meth sym_eval
		(orelse_meth existential
		(orelse_meth (repeat_meth generalise)
                         ml_ind_strat
	))))))))
	_
	true.

/*
compound induction (ind_strat IndType)
      ( then_meths (induction_meth IndType Scheme Subst)
                   (pair_meth (map_meth (step_case IndType)) (map_meth id_meth)) )
	_
	true.

compound induction ml_ind_strat
      ( then_meths (induction_meth mllists Scheme Subst)
                   (pair_meth (map_meth ml_step_case) (map_meth id_meth)) )
		 _		   
		true.
*/

compound induction (step_case mllists)
        ( cut_meth

	(then_meth
           ( then_meth (try_meth (repeat_meth all_i)) set_up_ripple )

	(then_meth

	
	(orelse_meth (then_meth
		(repeat_meth (patch_meth (wave_method outward R) wave_critic_strat))
			(orelse_meth
				fertilise
			(then_meth	
				(try_meth (repeat_meth 
		(patch_meth (wave_method inout R1) wave_critic_strat)))
				(try_meth fertilise))
		))
		(then_meth
		(repeat_meth (patch_meth (wave_method inout R1) wave_critic_strat))
		(try_meth fertilise)
	))

	(then_meth post_ripple (try_meth (repeat_meth all_e))))))
	_
	true.

atomic mlremovelists post_ripple
	trueGoal
	true
	true
	trueGoal
	notacticyet.


benchmark_plan mlremovelists Meth Query :-
        testloop (%interaction_mode command,
        (add_theory_to_induction_scheme_list objlists,
        (set_sym_eval_list [tremoveOne1, tremoveOne2, tremoveOne3, sremoveOne1, sremoveOne2, sremoveOne3, cons_functional],
        (set_wave_rule_to_sym_eval,
	(add_to_sym_eval_list [beta_reduction],
        pds_plan Meth Query))))).

end
