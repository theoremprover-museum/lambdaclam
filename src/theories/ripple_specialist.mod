module ripple_specialist.

accumulate arithmetic.
accumulate constructive_logic.

top_goal arithmetic ripple_test [(app forall (tuple [nat, (abs x\ (app
forall (tuple [nat, (abs y\ 
	(app eq (tuple [  
		(app plus (tuple [(app plus (tuple [n, y])), x])),
		(app plus (tuple [n, (app plus (tuple [y, x]))]))])))])))]))] 
  (app forall (tuple [nat, (abs x\ (app forall (tuple [nat, (abs y\
	(app eq (tuple [ 
		(app plus (tuple [(app plus (tuple [(app s n), y])), x])),
		(app plus (tuple [(app s n), (app plus (tuple [y, x]))]))])))])))])).

benchmark_plan arithmetic Meth Query :-
        testloop (set_sym_eval_list [idty, s_functional, leq1, leq2, leq_ss, assAnd1, prop3, prop4, prop5, prop6],
        (add_theory_defs_to_sym_eval_list arithmetic,
        (set_wave_rule_to_sym_eval,
        plan_this part_planner Meth Query depth_first_plan))).


end
