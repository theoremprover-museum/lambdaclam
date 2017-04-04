module pdd_prototype.

accumulate obj_lists.

has_otype pdd_prototype removeAll (arrow [nat, (olist nat)] (olist nat)).
has_otype pdd_prototype removeOne (arrow [nat, (olist nat)] (olist nat)).
has_otype pdd_prototype insert_Everywhere (arrow [nat, (olist nat)] (olist (olist nat))).
has_otype pdd_prototype ie (arrow [nat, (olist nat), (olist nat)] (olist (olist nat)))
has_otype pdd_prototype insert (arrow [nat, (olist nat)] (olist nat)).
has_otype pdd_prototype sort (arrow [(olist nat)] (olist nat)).
has_otype pdd_prototype once (arrow [(olist nat)] (olist nat)).
has_otype pdd_prototype onceOnly (arrow [(olist nat)] (olist nat)).
has_otype pdd_prototype count_list (arrow [nat, (olist nat)] nat).
has_otype pdd_prototype sorted (arrow [(olist nat)] bool).

definition pdd_prototype removeOne1 equiv
	trueP
	(app removeOne [X, onil])
	onil.
definition pdd_prototype removeOne2 equiv
	trueP
	(app removeOne [X, (app ocons [X, T])])
	T.
definition pdd_prototype removeOne3 equiv
	(app neq [X, H])
	(app removeOne [X, (app ocons [H, T])])
	(app ocons [H, (app removOne [X, T])]).

definition pdd_prototype removeAll1 equiv
	trueP
	(app removeAll [X, onil])
	onil.
definition pdd_prototype removeAll2 equiv
	trueP
	(app removeAll [X, (app ocons [X, T])])
	(app removeAll [X, T]).
definition pdd_prototype removeAll3 equiv
	(app neq [X, H])
	(app removeAll [X, (app ocons [H, T])])
	(app ocons [H, (app removOne [X, T])]).

top_goal pdd_prototype removeAllproblem []
	(app forall [nat, (abs x\
	(app forall [(olist nat), (abs l\
	(app neg [(app omember [x, (app removeAll [x, l])])]))]))]).


definition pdd_prototype insertEverywhere1 equiv
	trueP
	(app insertEverywhere [X, onil])
	(app ocons [(app ocons [X, onil]), onil]).
definition pdd_prototype insertEverywhere2 equiv
	trueP
	(app insertEverywhere [X, (app ocons [X1, XS])])
	(app ocons [(app ocons [X, (app ocons [X1, XS])]), 
		    (app insertEverywhere [X, XS])]).

definition pdd_prototype count_list1 equiv
	trueP
	(app count_list [X, onil])
	zero.
definition pdd_prototype count_list2 equiv
	trueP
	(app count_list [X, (app ocons [X, T])])
	(app suc [(app count_list [X, T])]).
definition pdd_prototype count_list3 equiv
	(app neq [X, H])
	(app count_list [X, (app ocons [H, T])])
	(app count_list [X, T]).


top_goal pdd_prototype insertEverywhereProblem []
	(app forall [(olist nat), (abs l1\
	(app forall [nat, (abs x\
	(app forall [(olist nat), (abs l\
	(app imp [(app omember [l, (app insertEverywere [x, l1])])
	          (app eq [(app count_list [x, l]), 
			   (app suc [(app count_list [x, l1])])])]))]))]))]).

definition pdd_prototype ie1 equiv
	trueP
	(app ie [N, R, onil])
	(app oapp [R, (app ocons [N, onil])]).
definition pdd_prototype ie2 equiv
	trueP
	(app ie [N, R, (app ocons [H, T])])
	(app ocons [(app ocons [N, (app ocons [H, T])]), 
                    (app oapp [(app ocons [R, onil]),
                               (app ie [N, (app oapp [R, (app ocons [H, onil])]), T])])]).

top_goal pdd_prototype ieProblem []
	(app forall [(olist nat), (abs l1\
	(app forall [(olist nat), (abs l2\
	(app forall [nat, (abs x\
	(app forall [(olist nat), (abs l\
	(app imp [(app omember [l, (app ie [x, l1, l2])])
	          (app eq [(app count_list [x, l]), 
			   (app oplus [(app suc [(app count_list [x, l2])]),
                                       (app count_list [x, l1])])])]))]))]))]))]).


definition pdd_prototupe insert1 equiv
	trueP
	(app insert [X, onil])
	onil.
definition pdd_prototype insert2 equiv
	(app leq [X, H])
	(app insert [X, (app ocons [H, T])])
	(app ocons [X, (app ocons [H, T])]).
definition pdd_prototype insert3 equiv
	(app neg (app leq [X, H]))
	(app insert [X, (app ocons [H, T])])
	(app ocons [H, (app insert [X, T])]).

definition pdd_prototype sort1 equiv
	trueP
	(app sort [onil])
	onil.
definition pdd_prototype sort2 equiv
	trueP
	(app sort [(app [X, XS])])
	(app insert [X, (app sort [XS])]).

definition pdd_prototype once1 equiv
	trueP
	(app once [onil])
	onil.
definition pdd_prototype once2 equiv
	(app eq [X1, X2])
	(app once [(app ocons [X1, (app ocons [X2, XS])])])
	(app once [(app ocons [X2, XS])]).
definition pdd_prototype once2 equiv
	(app neq [X1, X2])
	(app once [(app ocons [X1, (app ocons [X2, XS])])])
	(app oncs [(app ocons [X1, (app ocons [X2, (app once [XS])])])]).

definition pdd_prototype onceOnly1 equiv
	trueP
	(app onceOnly [onil])
	onil.
definition pdd_prototype onceOnly2 equiv
	trueP
	(app onceOnly [(app ocons [X, XS])
	(app once [(app sort [X, XS])]).

end