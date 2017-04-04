/*

File: ccs_hmf_syntax.mod
Author: James Brotherston
Description: Syntax declarations and pretty printing for:
	       - Hennessy-Milner modal logic for describing processes
               - CCS process expressions
Last Modified: 25th July 2002

*/

module ccs_hmf_syntax.

accumulate list_benchmarks.

local testdummy o -> o.
testdummy X.


%% Syntax declarations and pretty printing for actions 

is_otype ccs_hmf_syntax action [tau, allminus] [co].

has_otype ccs_hmf_syntax tau action.
has_otype ccs_hmf_syntax allminus action.
has_otype ccs_hmf_syntax co (action arrow action).

prettify_special (app co A) (blo 1 [str "co(", AA, str ")"]):-
  !, prettify_term A AA.


%% Syntax declarations for Hennessy-Milner modal formulas

is_otype ccs_hmf_syntax hmf [tt, ff] [and, or, box, diamond, exp_box, exp_diamond, hmf_comp].

has_otype ccs_hmf_syntax tt hmf.
has_otype ccs_hmf_syntax ff hmf.
has_otype ccs_hmf_syntax and (tuple_type [hmf, hmf] arrow hmf).
has_otype ccs_hmf_syntax or  (tuple_type [hmf, hmf] arrow hmf).
has_otype ccs_hmf_syntax box     (tuple_type [(olist action), hmf] arrow hmf).
has_otype ccs_hmf_syntax diamond (tuple_type [(olist action), hmf] arrow hmf).
has_otype ccs_hmf_syntax exp_box 
  ((tuple_type [(olist action), nat, hmf]) arrow hmf).
has_otype ccs_hmf_syntax exp_diamond 
  ((tuple_type [(olist action), nat, hmf]) arrow hmf).
has_otype ccs_hmf_syntax hmf_comp (hmf arrow hmf).

%% Pretty printing for HM formulas and lists of actions

prettify_special (app box (tuple [A,F])) 
  (blo 1 [str "[", AA, str "]", FF]):- 
  !, prettify_term A AA, prettify_term F FF.

prettify_special (app exp_box (tuple [A,N,F])) 
  (blo 1 [str "([", AA, str "]^", NN, str")", FF]):- 
  !, prettify_term A AA, prettify_term N NN, prettify_term F FF.

prettify_special (app diamond (tuple [A,F])) 
  (blo 1 [str "<", AA, str ">", FF]):- 
  !, prettify_term A AA, prettify_term F FF.

prettify_special (app exp_diamond (tuple [A,N,F])) 
  (blo 1 [str "(<", AA, str ">^", NN, str")", FF]):- 
  !, prettify_term A AA, prettify_term N NN, prettify_term F FF.

prettify_special (app hmf_comp F) (blo 1 [str "(", FF, str ")^c"]):-
  !, prettify_term F FF.

prettify_special (app ocons (tuple [A, onil])) (blo 1 [AA]):-
  !, prettify_term A AA.

prettify_special (app ocons (tuple [allminus,B])) (blo 1 [str "-", BB]):-
  !, prettify_term B BB.

prettify_special (app ocons (tuple [A,B])) (blo 1 [AA, str ",", BB]):-
  !, prettify_term A AA, prettify_term B BB. 


%% Syntax declarations for CCS process expressions

is_otype ccs_hmf_syntax ccs [ccs_nil] [dot, ccs_plus, bar, slash].

has_otype ccs_hmf_syntax ccs_nil ccs.
has_otype ccs_hmf_syntax dot (tuple_type [action, ccs] arrow ccs).
has_otype ccs_hmf_syntax ccs_plus (tuple_type [ccs, ccs] arrow ccs).
has_otype ccs_hmf_syntax bar (tuple_type [ccs, ccs] arrow ccs).
has_otype ccs_hmf_syntax slash (tuple_type [ccs, olist action] arrow ccs).


%% Pretty printing for CCS process expressions

prettify_special (ccs_nil) (str "0").
  
prettify_special (app dot (tuple [A,E])) (blo 1 [AA, str ".", EE]):- 
  !, prettify_term A AA, prettify_term E EE.

prettify_special (app ccs_plus (tuple [E,F])) 
  (blo 1 [str "(", EE, str " + ", FF, str ")"]):- 
  !, prettify_term E EE, prettify_term F FF.

prettify_special (app bar (tuple [E,F])) 
  (blo 1 [str "(", EE, str " | ", FF, str")"]):- 
  !, prettify_term E EE, prettify_term F FF.

prettify_special (app slash (tuple [E,J]))
  (blo 1 [EE, str "\\{", JJ, str "}"]):- 
  !, prettify_term E EE, prettify_term J JJ.


%% Syntax declaration and pretty printing for the satisfiability relation

has_otype ccs_hmf_syntax satisfies (tuple_type [ccs, hmf] arrow bool).

prettify_special (app satisfies (tuple [E,M])) 
  (blo 1 [EE, str " |== ", brk 1, MM]):- 
  !, prettify_term E EE, prettify_term M MM.



end