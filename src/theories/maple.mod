
module maple.

accumulate otter.

type x osyn.
type maple_simplify goal -> goal -> o.
type formula_is_arithmetic osyn -> o.

type list_is_arithmetic list(osyn) -> o.
type my_member osyn -> list(osyn) -> o.
type result_to_term string -> osyn -> o.

%type maple_simplify osyn -> osyn -> o.

top_goal maple maple_goal []
        (app eq (tuple [(app plus (tuple [zero, x])), x])).

%atomic constructive_logic imp_i 
%           (seqGoal (H >>> (app imp (tuple [A, B])))) 
%           true
%           true 
%           (seqGoal ((( A::H) >>> B))) 
%           notacticyet.

atomic maple maple_simplify_meth
        G   %%(seqGoal (H >>> G))
        (maple_simplify G Gprime)
	true
        Gprime %%	(seqGoal (H >>> Gprime))   %trueGoal
	notacticyet.

% string_to_term "(app eq (tuple [<lc-0-1>, <lc-0-1>]))" X.
% string_to_term "(app eq (tuple <lc-0-1>::<lc-0-1>::nil))" X.

maple_simplify (ripGoal (Hyps >>> Formula) Skel Emb) Result:-
%        pprint_string "ripGoal: ",
%        pprint_term  Formula,
        
        maple_simplify (seqGoal (Hyps >>> Formula)) (seqGoal (Hyps >>> NewFormula)),
        
        Result = (ripGoal (Hyps >>> NewFormula) Skel Emb),
        pprint_goal Result.        


maple_simplify (seqGoal (Hyps >>> Formula)) Result:-
%        pprint_string "seqGoal: ",
%        pprint_term Formula,

        formula_is_arithmetic Formula,
        
        mathweb_get_service "MAPLE" MapleService, 
        output std_out "service: ",
        output std_out MapleService,
        output std_out "\n",
        flush std_out,

        print_open_math Formula OMFormula, 
        OMObj is "'OMOBJ'(" ^ OMFormula ^ ")",        
        Method is "simplifyTerm(" ^ OMObj ^ ")",
        
        mathweb_apply MapleService "simplifyTerm" [["1", OMObj]] 100 ResultList,	
        (ResultString::nil)::nil = ResultList,
        pprint_string ResultString,!,
        result_to_term ResultString Term,
        pprint_string "after result2term",
                                                %        printterm std_out Term,
%        print "\n",
        flush std_out,
        Result = (seqGoal (Hyps >>> Term)),
        printterm std_out Result,
        print "\n",
        flush std_out,
        mathweb_leave_service MapleService,
        print "service MAPLE left.\n",
        flush std_out.


result_to_term "error" _:-!, 
        pprint_string "error case",
        fail.

result_to_term ResultString Term:-
        pprint_string "Before string_to_term",
        not (ResultString = "error"),
        string_to_term ResultString Term,
        pprint_string "bar".

triv_var A :-
	not (not (A = zero)),not (not (A = one)),
        print "triv_var:",
        pprint_term A.

triv_atom A :-
	not (triv_var A),
	not (A = app _ _).

list_is_arithmetic (X::Xr):-!, 
        pprint_string "list head:",
        pprint_term X,
        formula_is_arithmetic X,
        list_is_arithmetic Xr.

list_is_arithmetic nil:-!, true.

formula_is_arithmetic (app (abs X\ (P X)) B):- 
        not (B = (tuple [_,_])),
        !,
        pprint_string "app_abs_is_arithmetic: ",
        pprint_term X,
	pprint_term B,
        formula_is_arithmetic (P X),
        formula_is_arithmetic B.

formula_is_arithmetic (abs X\ (P X)):-!,
        pprint_string "abs_is_arithmetic: ",
	pprint_term (P X),
        true.

formula_is_arithmetic (app imp _):- !,
        pprint_string "app_imp_fail",
        fail.

formula_is_arithmetic (app forall _):- !,
        pprint_string "app_forall_fail",
        fail.

formula_is_arithmetic (app A (tuple List)):- !,
        not (A = imp),
        pprint_string "formula_is_arithmetic app multi-ary: ",
        pprint_term (app A (tuple List)),
        is_arithmetic A,!,
        list_is_arithmetic List.
%        mappred List (X \ Y \ print "mapping: \n", pprint_term X, formula_is_arithmetic X) _.

formula_is_arithmetic (app A B):- 
	not (A = (abs _)),
	not (B = (tuple [_,_])),
	!,
        pprint_string "formula_is_arithmetic app unary: ",
        pprint_term (app A B),
        is_arithmetic A,!,
        pprint_string "after",
        formula_is_arithmetic B.

formula_is_arithmetic X:- 
        triv_atom X,
	!,
	pprint_string "triv_atom:  ",
	pprint_term X.

formula_is_arithmetic X:- 
        not (triv_atom X),
	!,
        pprint_string "!!!not triv_var:",
	pprint_term X.

compound induction (induction_top IndType) (complete_meth
		(repeat_meth
		(orelse_meth trivials
		(orelse_meth allFi
	 	(orelse_meth taut
            	(orelse_meth sym_eval
		(orelse_meth maple_simplify_meth 
		(orelse_meth existential
		(orelse_meth (repeat_meth generalise)
                         (ind_strat IndType)
	)))))))))
	_
	true.

compound induction fertilise
        ( cut_meth 
	    ( then_meth (try_meth piecewise_fertilisation)
            (orelse_meth ( orelse_meth
                    (orelse_meth maple_simplify_meth
		    (repeat_meth fertilisation_strong))
                    (repeat_meth fertilisation_weak) )
			truegoalmeth)))
	_
	true.

%      my_member X [zero, one, two, three, four, five, eight, ten].
%
%formula_is_arithmetic X:-
%	has_otype _ X _.

formula_is_arithmetic (_ arrow _).
formula_is_arithmetic (tuple_type _).

%formula_is_arithmetic X:- true.

is_arithmetic (abs X):-
        pprint_string "foo".

is_arithmetic Functor:-
        pprint_string "is_arithmetic? ", 
        pprint_name Functor,
        List = [s, summation, fibonacci, plus, minus, otimes, odiv, exp, sqrt, eq, nat_to_real],
        my_member Functor List,!.

my_member X (X::Lr):-!,
        pprint_string "is arithmetic!*****".

my_member X (Y::Lr) :- 
        not (X = Y),
        !,
        my_member X Lr.

my_member X nil:- pprint_string "not found", fail.
        
end

