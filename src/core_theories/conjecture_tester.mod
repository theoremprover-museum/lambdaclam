/*

File: conjecture_tester.mod
Author: Louise Dennis
Description: A conjecture tester (currently based around cuts) - see BBNOTE 1223.
Last Modified: 11th December 2000

*/

module conjecture_tester.

accumulate test_set_gen, logic_eq_constants.

local ground_goals int -> (list osyn) -> osyn -> (list osyn) -> o.
local evaluate_expression (list rewrite_rule) -> (list osyn) -> osyn -> osyn -> int -> (list context) -> o.


%% Compound Method - run through proof plan on ground terms.

%% Orders is a list of the complexities of terms desired.
%% Strategy is the proof strategy to be used for testing
%% Label is the desired outcome

%% generate_ground_instances, as expected, generates ground instances
%% of the goal.
%% pick_label "always" succeeds if Label is variable.
%% the only way it can fail is if Label is instantiated.
%% reassert G then reasserts the original Goal
compound conjecture_tester (formula_tester Orders Strategy Label)
	(cond_meth contains_meta_var_goal id_meth 
	(then_meth (generate_ground_instances Orders)
		(pair_meth (map_meth (then_meth Strategy (pick_label Label))) id_meth)))
	_
	true.

atomic conjecture_tester evaluate 
	(seqGoal (H >>> G) Context)
	(sym_eval_rewrites_list List,
	(((member (banned BList) Context), 
		  partition_rw BList List _ Rest); 
           (not (member (banned _) Context), Rest = List)), 
	   evaluate_expression Rest H G G1 50 Context, !)
	true
	(seqGoal (H >>> G1) Context)
	notacticyet.

evaluate_expression _ _ trueP trueP _ C:- !.
evaluate_expression _ _ falseP falseP _ C:- !.
evaluate_expression Rest H G G1 N C:-
	N > 1,
	rewrite_with_rules_eval (beta_reduction::(type_constructors::(neg1::(neg2::(and1::(and2::(and3::(and4::(or1::(or2::(or3::(or4::(imp1::(imp2::(imp3::(iff1::Rest)))))))))))))))) G GP Cond, 
	trivial_condition Cond H, !,
	N1 is N - 1,
	evaluate_expression Rest H GP G1 N1 C.
evaluate_expression L H G G1 N C:-
	N > 1,
	memb_and_rest (hyp Hyp _) H Rest,
	beta_reduce Rest Hyp HG,
	rewrite_using HG G GP red 2 Cond,
	trivial_condition Cond H, !,
	(not (G = GP)),
	N1 is N - 1,
	evaluate_expression L H GP G1 N1 C.
evaluate_expression _ _ G G _ _.


axiom conjecture_tester type_constructors equiv 
	trueP
	(app eq [X, Y])
	falseP:-
		is_otype _ Type BaseConstructors StepConstructors,
		((member X BaseConstructors, XCon = X);  
                 (X = (app XCon _), (member XCon BaseConstructors; member XCon StepConstructors))),
		((member Y BaseConstructors, YCon = X);  
                 (Y = (app YCon _), (member YCon BaseConstructors; member YCon StepConstructors))),
		!, not (XCon = YCon).




%% Method - returns a false goal if the conjecture tester finds a
%% counter example.
atomic conjecture_tester (generate_ground_instances Orders)
	(seqGoal (H >>> G) Context)
	(map_app Orders (X\ Y\ ground_goals X H G Y) NGs,
	 mapfun NGs (G1\ (seqGoal (H >>> G1) Context)) NG1,
	 mapbuild (G1\ G2\ (G1 ** G2)) NG1 NewGoals, !)
	true
	(NewGoals ** (seqGoal (H >>> G) Context))
	notacticyet.

atomic conjecture_tester (pick_label (label_truth 1 _ _))
	trueGoal
	true
	true
	trueGoal
	notacticyet.

atomic conjecture_tester (pick_label (label_truth _ 1 _))
	falseGoal
	true
	true
	trueGoal
	notacticyet.

atomic conjecture_tester (pick_label (label_truth 1 _ _))
	(seqGoal (_ >>> G) _)
	(stripping_to_bool G trueP)
	true
	trueGoal
	notacticyet.

atomic conjecture_tester (pick_label (label_truth _ 1 _))
	(seqGoal (_ >>> G) _)
	(stripping_to_bool G falseP)
	true
	trueGoal
	notacticyet.

atomic conjecture_tester (pick_label (label_truth _ _ 1))
	G
	(not (G = trueGoal),
	(not (G = seqGoal (_ >>> G1) _, stripping_to_bool G1 trueP)),
	( not (G = seqGoal (_ >>> G1) _, stripping_to_bool G1 falseP)),
	 (not (G = falseGoal)))
	true
	trueGoal
	notacticyet.

local stripping_to_bool osyn -> osyn -> o.
stripping_to_bool X X.
stripping_to_bool (app forall [T, (abs F T)]) X:-
	pi x\ (stripping_to_bool (F x) X).

%% Strips of universal quantifers and substitutes test instances.
ground_goals Order H G Gs:-
	env_otype_inst_types G H bool,
	memb_and_rest (hyp (otype_of A Type) _) H Rest, 
	subterm_of G A _, !,
	cut Order Type Subs, !,
	((Order > 0, OrderB is Order - 1); OrderB = 0),
	map_app Subs (X\ Y\ sigma G1\ replace_with G A X G1, 
                ground_goals OrderB Rest G1 Y) Gs.
ground_goals Order H (app forall [Type, (abs (X\ (Term X)) Type)]) Gs:-
	cut Order Type Subs, !,
	((Order > 0, OrderB is Order - 1); OrderB = 0),
	map_app Subs (X\ Y\ ground_goals OrderB H (Term X) Y) Gs.
ground_goals _ H Term [Term]:-
	(not (member (hyp (otype_of X Type) _) H, subterm_of Term X _)),
	(not (Term = (app forall _))), !.

%% Some test conjectures.

local map_app (list A) -> (A -> (list B)-> o) -> (list B) -> o.

map_app nil _ nil.
map_app (H1::T1) F Out:-
	F H1 L, !,
	map_app T1 F Tl,
	append L Tl Out.

contains_meta_var_goal (seqGoal (H >>> G) _):-
	subterm_of G (app F _) _, headvar_osyn F.
contains_meta_var_goal (seqGoal (H >>> G) _):-
	for_one H (X\ sigma F\ (subterm_of X (app F _) _, headvar_osyn F)) _.

/* truth tables */
definition constructive_logic neg1 trueP (app neg [trueP]) falseP.
definition constructive_logic neg2 trueP (app neg [falseP]) trueP.
definition constructive_logic and1 trueP (app and [falseP, _]) falseP.
definition constructive_logic and2 trueP (app and [_, falseP]) falseP.
definition constructive_logic or1 trueP (app or [trueP, _]) trueP.
definition constructive_logic or2 trueP (app or [_, trueP]) trueP.
definition constructive_logic imp1 trueP (app imp [falseP, _]) trueP.
definition constructive_logic imp2 trueP (app imp [_, trueP]) trueP.

/* ? should these count as definitions ? */

lemma constructive_logic or3 equiv trueP (app or [falseP, X]) X.
lemma constructive_logic or4 equiv trueP (app or [X, falseP]) X.
lemma constructive_logic and3 equiv trueP (app and [X, trueP]) X.
lemma constructive_logic and4 equiv trueP (app and [trueP, X]) X.
lemma constructive_logic iff1 equiv trueP (app iff [trueP, X]) X.
lemma constructive_logic imp3 equiv trueP (app imp [trueP, X]) X.

axiom constructive_logic beta_reduction equiv
	trueP
	(app (abs (x\ (F x)) _) [Y])
	(F Y).
axiom constructive_logic beta_reduction equiv
	trueP
	(app (abs (x\ (F x)) _) (H::T))
	(app (F H) T).

end
