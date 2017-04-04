module whisky.

accumulate arithmetic.
accumulate constructive_logic.

local whiskydummy o -> o.
whiskydummy X.
local whiskydummy2 o -> o.
whiskydummy2 X.
local whiskydummy3 o -> o.
whiskydummy3 X.
local whiskydummy4 o -> o.
whiskydummy4 X.
local whiskydummy5 o -> o.
whiskydummy5 X.
local whiskydummy6 o -> o.
whiskydummy6 X.

has_otype whisky whisky_p (arrow [nat, nat] bool).
has_otype whisky whisky_h (arrow [nat] nat).
 




lemma whisky whisky1 equiv
	trueP
	(app whisky_p  [zero, zero])
	trueP.
lemma whisky whisky2 equiv
	trueP
	(app whisky_p  [(app whisky_h [X]), zero])
	(app whisky_p  [X, zero]).
lemma whisky whisky3 equiv
	trueP
	(app whisky_p  [X, (app s [Y])])
	(app whisky_p  [(app whisky_h [X]), Y]).


lemma whisky whiskyp1 equiv
	trueP
	(app whisky_p2  [zero, zero])
	trueP.
lemma whisky whiskyp2 equiv
	trueP
	(app whisky_p2  [(app whiskyh [X]), zero])
	(app whisky_p2  [(app s [X]), zero]).
lemma whisky whiskyp3 rtol
	trueP
	(app whisky_p2  [X, (app s [Y])])
	(app whisky_p2  [(app (app fun_compose  [whiskyh, whiskyk]) [X]), Y]).
lemma whisky whiskyp4 equiv
	trueP
	(app whiskyk [X])
	(app s [(app s [(app s [X])])]).
lemma whisky whiskyp5 equiv
	trueP
	(app whisky_p2  [(app s [(app s [X])]), zero])
	(app whisky_p2  [X, zero]).


has_otype whisky w2 (arrow [nat, nat] bool).
has_otype whisky wk (arrow [nat] nat).
has_otype whisky wh (arrow [(arrow [nat] nat), nat] nat).
lemma whisky w21 equiv
	trueP
	(app w2  [zero, zero])
	trueP.
lemma whisky w24 equiv
	trueP
	(app w2  [(app wk [N]), zero])
	(app w2  [N, zero]).
lemma whisky w22 equiv
	trueP
	(app w2  [(app wh  [F, X]), zero])
	(app w2  [X, zero]).
lemma whisky w23 equiv
	trueP
	(app w2  [(app wh  [F, X]), (app s [Y])])
	(app w2  [(app wh  [F, (app F [X])]), Y]).



lemma whisky assplem equiv
	trueP
	(app plus  [(app plus  [X, Y]), Z])
	(app plus  [X, (app plus  [Y, Z])]).
lemma whisky quantifier_elim rtol
	trueP
	(app forall  [Type, (abs (X\ P) Type)])
	P.

lemma whisky fun_iter4 equiv
        trueP
        (app fun_compose  [F, (app fun_iter  [N, F])])
        (app fun_iter  [(app s [N]), F]).



induction_scheme whisky fun_struct
   nat
   (dom (a \ (repl a (app s [a]))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall  [nat, (abs (n\ Prop (app (abs (m\ (app (app fun_iter  [m, F]) [B])) nat) [n])) nat)])) Context)
   (
   % Base case
        (seqGoal (H >>> (Prop B)) Context)
    **
   % Step case
    (allGoal nat n\ (seqGoal ((hyp (otype_of n nat) nha)::(hyp (Prop (app (app fun_iter [n, F]) [B])) ind_hyp)::H >>> (Prop (app F [(app (app fun_iter  [n, F]) [B])]))) Context))
        ).


induction_scheme whisky nat_struct2
   nat
   (dom (a \ (repl a (app s [a]))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall  [nat, (abs Prop nat)])) Context)
   (
   % Base case
        (seqGoal (H >>> (Prop zero)) Context)
    **
   % Step case
    ((allGoal nat z\ (seqGoal ((otype_of z nat)::(hyp (Prop z) ind_hyp)::H >>> (Prop (app s [z]))) Context)))
        ).

/*
compound whisky (ind_strat whisky_ind)
      ( then_meths (induction_meth with_critics Scheme Subst)
                   (pair_meth (map_meth id_meth) (map_meth (step_case with_critics))))
	_
	true.
*/

top_goal whisky fun_iter_g1 []
	(app forall  [(arrow [nat] nat), (abs (f\
		(app forall  [nat, (abs (x\
	(app eq  [
		(app (app fun_iter  [zero, f]) [x]),
		x])) nat)])) (arrow [nat] nat))]).

%% Victim of Overgeneralisation!
top_goal whisky fun_iter_g2 []
	(app forall  [(arrow [nat] nat), (abs (f\
		(app forall  [nat, (abs (n\
			(app forall  [nat, (abs (x\
	(app eq  [
		(app f [(app (app fun_iter  [n, f]) [x])]),
		(app (app fun_iter  [n, f]) [(app f [x])])])) nat)])) nat)])) (arrow [nat] nat))]).

top_goal whisky whisky_problem []
	(app forall  [nat, (abs (y\
		(app whisky_p  [zero, y])) nat)]).

top_goal whisky whisky_problem2 []
	(app forall  [nat, (abs (y\
		(app w2  [(app wh [wk, zero]), y])) nat)]).

top_goal whisky whisky_problem3 []
	(app forall  [nat, (abs (y\
		(app whisky_p2  [zero, y])) nat)]).

top_goal whisky whisky_gen_problem []
	(app forall  [nat, (abs (y\
		(app forall  [nat, (abs (n\
	(app whisky_p  [(app (app fun_iter [n, whisky_h]) [zero]),
			      y])) nat)])) nat)]).

fun_iter1plan:-	
	(sym_eval_list [fun_iter1, beta_reduction, idty] =>
		pds_plan (induction_top normal_ind) fun_iter_g1).


fun_iter2plan:-
	(induction_schemes_list [nat_struct] =>
		(sym_eval_list [fun_iter1, fun_iter2, fun_compose1, beta_reduction, idty] =>
		(wave_rule_list [fun_iter1, fun_iter2, fun_compose1, beta_reduction, idty] =>
	pds_plan (induction_top normal_ind) fun_iter_g2))).



benchmark_plan whisky Meth Query :-
        testloop (%interaction_mode command,
        (set_induction_scheme_list [nat_struct],
        (set_sym_eval_list [quantifier_elim, assplem, idty, whisky1, whisky2, whisky3, fun_compose1, fun_iter1, plus1, plus2, times1, times2, exp1, exp2, w21, w22, w23, w24, whiskyp1, whiskyp2, whiskyp3, whiskyp5, whiskyp4],
        (set_wave_rule_to_sym_eval,
	(add_to_wave_rule_list [fun_iter2, fun_iter4],
	(add_to_sym_eval_list [beta_reduction],
        pds_plan Meth Query)))))).

whiskyproblem:-
	(induction_schemes_list [nat_struct] =>
		(sym_eval_list [fun_iter1, fun_iter2, fun_compose1, beta_reduction, idty, whisky1 ] =>
		(wave_rule_list [fun_iter1, fun_iter2, fun_compose1, beta_reduction, idty] =>
	pds_plan (induction_top with_critics) whisky_problem))).

whiskyproblem2:-
	(induction_schemes_list [nat_struct] =>
		(sym_eval_list [fun_iter1, fun_iter2, fun_compose1, beta_reduction, idty] =>
		(wave_rule_list [fun_iter1, fun_iter2, fun_compose1, beta_reduction, idty] =>
	pds_plan (induction_top normal_ind) whisky_gen_problem))).

	
	

end
	
