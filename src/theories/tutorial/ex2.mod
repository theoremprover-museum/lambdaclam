module ex2.

accumulate objlists.
accumulate constructive_logic.

/*
local ex2dummy osyn -> o.
ex2dummy X.
local ex2dummy2 osyn -> o.
ex2dummy2 X.
*/

has_otype ex2 qrev (arrow [(olist X), (olist X)] (olist X)).

definition ex2 qrev1 
	trueP
	(app qrev  [onil, L])
	L.
definition ex2 qrev2
	trueP
	(app qrev  [(app ocons  [H, T]), L])
	(app qrev  [T, (app ocons  [H, L])]).

lemma ex2 oapp_lemma equiv
	trueP
        (app oapp  [(app qrev  [L2, L3]), L4])
        (app qrev  [L2, (app oapp  [L3, L4])]).



top_goal ex2 orevqrev []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
			(app eq  [
	(app oapp  [(app orev [x]), y]),
	(app qrev  [x, y])])) (olist nat))])) (olist nat))]).

top_goal ex2 revqrevlemma []
	(app forall  [(olist nat), (abs (x\
		(app forall  [(olist nat), (abs (y\
			(app forall  [(olist nat), (abs (z\
	(app eq  [
	(app oapp  [(app qrev  [x, y]), z]),
	(app qrev  [x, (app oapp [y, z])])])) (olist nat))])) (olist nat))])) (olist nat))]).

orevqrevplan:-
        (induction_schemes_list [list_struct] =>
                (sym_eval_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2, oapp_lemma] =>
                (wave_rule_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2, oapp_lemma] =>
                pds_plan (induction_top normal_ind) orevqrev))).

revqrevlemmaplan:-
        (induction_schemes_list [list_struct] =>
                (sym_eval_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2] =>
                (wave_rule_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2] =>
                pds_plan (induction_top normal_ind) revqrevlemma))).
end

