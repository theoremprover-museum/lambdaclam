% **************************************************************
%
% (S)GS framework for using decision procedures
%
% Author: Predrag Janicic
% June 2001
% July 2002
%
% Based on papers:
%
% Janicic P. and Bundy A.:
% "General setting for the flexible combining and incorporating
% decision procedures into theorem provers", 2002. To appear in JAR.
%
% Janicic P. and Bundy A.:
% "Strict general setting for building decision procedures
% into theorem provers", 2001. Presented as a short paper
% at IJCAR '01. Available in IJCAR '01 Short papers proceedings.
% Longer version also available as DAI Research Paper ??
%
% Note that GS framework is formulated as proof-refutation system
% and therefore all GS rules here are dual to the corresponding
% rules in GS paper
%
% **************************************************************

module gs_framework.

% in rewriting:
% %accumulate embed. (in order to be able to compile).
accumulate rewriting.
accumulate constructive_logic.
%accumulate logic_eq_constants.
accumulate planner.

%This doesn't work and it should (string_to_term problem)
%
%pds_plan (tecton_style_scheme [ gs_pia ]) decisionSGS1a.
%pds_plan (shostak_style_scheme [ gs_pia ]) decisionSGS2.
%pds_plan (tecton_style_scheme [ gs_pia ]) decisionSGS2.
%pds_plan (shostak_style_scheme [ gs_pia ]) decisionSGS4.
%pds_plan (tecton_style_scheme [ gs_pia ]) decisionSGS4.
%pds_plan (shostak_style_scheme [ gs_pia ]) decisionSGS5.
%pds_plan (tecton_style_scheme [ gs_pia ]) decisionSGS6.
%pds_plan (tecton_style_scheme [ gs_pia ]) decisionSGS7.
%pds_plan (shostak_style_scheme [ gs_pia ]) decisionSGS7.
%pds_plan (tecton_style_scheme [ gs_lemmas, gs_pia ]) decisionSGS9.
%pds_plan (tecton_style_scheme [ gs_lemmas, gs_pia ]) decisionSGS9a.
%pds_plan (tecton_style_scheme [ gs_lemmas, gs_pia ]) decisionSGS10.

%This doesn't work and it should (bad socket communication)
%
%pds_plan (nelson_oppen_style_scheme [ gs_objlists, gs_pure_equality, gs_pia ]) decisionSGS1.
%pds_plan (nelson_oppen_style_scheme [ gs_objlists, gs_pure_equality, gs_pia ]) decisionSGS1c.

%This works:
%
%pds_plan (tecton_style_scheme [ gs_pia, gs_lemmas ]) decision4.
%pds_plan (tecton_style_scheme [ gs_pia ]) decision6.
%pds_plan (nelson_oppen_style_scheme [ gs_pia , gs_pure_equality ]) decision6.
%pds_plan (shostak_style_scheme [ ]) decision6.
%pds_plan (shostak_style_scheme [ ]) decision7.
%pds_plan (nelson_oppen_style_scheme [ gs_pia , gs_pure_equality ]) decision8.
%pds_plan (shostak_style_scheme [ gs_pia ]) decision_assp.
%
%pds_plan (nelson_oppen_style_scheme [ gs_objlists, gs_pure_equality, gs_pia ]) decisionSGS1a.
%pds_plan (nelson_oppen_style_scheme [ gs_pure_equality, gs_pia ]) decisionSGS2.
%pds_plan (nelson_oppen_style_scheme [ gs_pure_equality, gs_pia ]) decisionSGS3.
%pds_plan (shostak_style_scheme [ gs_pia ]) decisionSGS3.
%pds_plan (tecton_style_scheme [ gs_pia ]) decisionSGS3.
%pds_plan (nelson_oppen_style_scheme [ gs_pure_equality, gs_pia ]) decisionSGS4.
%pds_plan (nelson_oppen_style_scheme [ gs_pure_equality, gs_pia ]) decisionSGS5.
%pds_plan (nelson_oppen_style_scheme [ gs_pure_equality, gs_pia ]) decisionSGS6.
%pds_plan (nelson_oppen_style_scheme [ gs_pure_equality, gs_pia ]) decisionSGS7.


compound gs_framework (nelson_oppen_style_scheme Theories)
(complete_meth
(repeat_meth
	(then_meth
		(try_meth (repeat_meth all_i))
		(then_meth
			(convert_to_cnf)
			(then_meth
				(try_meth (repeat_meth and_i))
				(then_meth
					(try_meth (then_meth (simpl) (trivial)))
					(then_meth
						(try_meth (purify Theories))
						(then_meth
							(try_meth (valid Theories))
							(then_meth
								(entail nelson_oppen Theories)
								(try_meth (repl_eq)))))))))))
_
true.


compound gs_framework (shostak_style_scheme Theories)
(complete_meth
(repeat_meth
	(then_meth
		(try_meth (repeat_meth all_i))
		(then_meth
			(convert_to_cnf)
			(then_meth
				(try_meth (repeat_meth and_i))
				(then_meth
					(try_meth (then_meth (simpl) (trivial)))
					(then_meth
						(try_meth (purify_e Theories))
						(then_meth
							(try_meth (ccc))
							(then_meth
							(try_meth (entail shostak Theories))
							(try_meth (replace)))))))))))
_
true.



compound gs_framework (tecton_style_scheme  Theories)
(complete_meth
(repeat_meth
	(then_meth
		(try_meth (repeat_meth all_i))
		(then_meth
			(convert_to_cnf)
			(then_meth
				(try_meth (repeat_meth and_i))
				(then_meth
					(try_meth (then_meth (simpl) (trivial)))
					(then_meth
						(try_meth (purify_e Theories))
						(then_meth
							(try_meth (then_meth (ccc) (trivial)))
							(then_meth
							(try_meth (then_meth (entail hodes Theories) (trivial)))
							(then_meth
							(try_meth (lemma_invocation))
							(try_meth (replace)))
)))))))))
_
true.



% compound gs_framework entailment_repeat (repeat_meth (entail nelson_oppen [arithmetic])) true.


atomic gs_framework check
	(seqGoal (H >>> trueP))
	true
	true
	(trueGoal)
	notacticyet.

atomic gs_framework simpl
	(seqGoal (H >>> G))
	(gs_simplify nil G GG)
	true
	(seqGoal (H >>> GG))
	notacticyet.

atomic gs_framework (simpl_t Theory)
	(seqGoal (H >>> G))
	(gs_simplify_t H Theory G GG)
	true
	(seqGoal (H >>> GG))
	notacticyet.

atomic gs_framework ccc
	(seqGoal (H >>> G))
	(gs_ccc G GG)
	true
	(seqGoal (H >>> GG))
	notacticyet.

atomic gs_framework replace
	(seqGoal (H >>> G))
	(gs_repl G GG)
	true 
	(seqGoal (H >>> GG))
	notacticyet.


atomic gs_framework repl_eq
	(seqGoal (H >>> G))
	(gs_repl_eq G GG)
	true
	(seqGoal (H >>> GG))
	notacticyet.

atomic gs_framework (purify Theories)
        (seqGoal (H >>> G))
	(gs_abspplus Theories H G GG AbsVars,
	not (AbsVars = nil),
	gs_make_goal H GG AbsVars NewGoal)
        true
	( NewGoal )
        notacticyet.


atomic gs_framework (purify_e Theories)
        (seqGoal (H >>> G))
	(append Theories [ gs_pure_equality ] Theories1,
	gs_abspplus Theories1 H G GG AbsVars,
	not (AbsVars = nil),
	gs_make_goal H GG AbsVars NewGoal)
        true
	( NewGoal )
        notacticyet.


atomic gs_framework lemma_invocation
        (seqGoal (H >>> G))
	(gs_lemma [ gs_pia ] H G GG [ [ V , T ] ],
	NewGoal = (seqGoal ( ((otype_of V T)::H) >>> GG )))
        true
	( NewGoal )
        notacticyet.

atomic gs_framework (entail nelson_oppen TheoryList)
        (seqGoal (H >>> G))
	(gs_entail_no TheoryList H G ImplicitDisequality,
	NewGoal = (app or (tuple [ G , ImplicitDisequality ])))
        true
	( seqGoal (H >>> NewGoal) )
        notacticyet.

atomic gs_framework (entail shostak Theories)
        (seqGoal (H >>> G))
	(gs_member gs_pia Theories,
	gs_entail_shostak H [ gs_pia ] G GG,
	(not (G = GG)))
        true
	( seqGoal (H >>> GG) )
        notacticyet.

atomic gs_framework (entail cooper Theories)
        (seqGoal (H >>> G))
	(gs_member gs_pia Theories,
	 gs_entail_cooper H gs_pia G GG)
        true
	( seqGoal (H >>> GG ) )
        notacticyet.


atomic gs_framework (entail hodes Theories)
        (seqGoal (H >>> G))
	(gs_member gs_pia Theories,
	 gs_entail_hodes H gs_pia G GG)
        true
	( seqGoal (H >>> GG ) )
        notacticyet.



atomic gs_framework (valid Theories)
        (seqGoal (H >>> G))
	(gs_valid_t H Theories G)
        true
	( trueGoal )
        notacticyet.



local gs_make_goal_ ((list X) -> osyn -> goal -> o).
gs_make_goal_ H G (seqGoal (H >>> G)) :- !.
gs_make_goal_ H G (seqGoal (((otype_of Var Type)::H1) >>> G1)) :- !,
	gs_make_goal_ H G (seqGoal (H1 >>> G1)).

local dummysyntax osyn.
local gs_make_goal ((list X) -> osyn -> (list Y) -> goal -> o).
gs_make_goal H G nil NG :- gs_make_goal_ H G NG.
gs_make_goal H G ([Var, Type]::L) (allGoal Type V\ (NG1 V)) :- 
	Var = dummysyntax,
	G = (GFun dummysyntax),
	(not (subterm_of (abs x\ (GFun x)) dummysyntax _)),!,
	(pi x\ (gs_make_goal ((otype_of x Type)::H) (GFun x) L (NG1 x))).


atomic gs_framework convert_to_cnf
	(seqGoal (H >>> G))
	(gs_prenex_cnf G NewG)
	true
	(seqGoal (H >>> NewG))
	notacticyet.

top_goal gs_framework decision1 [] 
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app forall (tuple [nat, (abs c\
	(app forall (tuple [nat, (abs d\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app and (tuple [
				(app eq (tuple [a, b])),
				(app eq (tuple [c, d]))])),
			(app eq (tuple [(app f (app plus (tuple [a, c]))),
					(app f (app plus (tuple [b, d])))]))])))])))])))])))])))])).

top_goal gs_framework decision2 [] 
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app forall (tuple [nat, (abs c\
	(app forall (tuple [nat, (abs d\
	(app forall (tuple [(nat arrow nat), (abs f\

	(app and (tuple [
		(app or (tuple [(app neg (app eq (tuple [a, b]))),
				(app eq (tuple [(app f a), (app f b)]))])),
		(app imp (tuple [(app and (tuple [
				(app eq (tuple [a, b])),
				(app eq (tuple [c, d]))])),
			(app eq (tuple [(app f (app plus (tuple [a, c]))),
					(app f (app plus (tuple [b, d])))]))]))])))])))])))])))])))])).

top_goal gs_framework decision3 [] 
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app forall (tuple [nat, (abs c\
	(app forall (tuple [(nat arrow nat), (abs f\
	(app imp (tuple [ (app and (tuple [ (app eq (tuple [ a , b ])),
					    (app eq (tuple [ b , c ])) ])) ,
			  (app eq (tuple [ a , c ])) ] )) ) ])) )])))])))])).


top_goal gs_framework decision4 [] 
	(app forall (tuple [nat, (abs a\
	(app leq (tuple [ (app min a), (app max a)])))])).


top_goal gs_framework decision5 []
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app imp (tuple [ (app eq (tuple [ (app maxpair (tuple [ a , b ])) , a ])) , (app eq (tuple [ (app minpair (tuple [ a , b ])) , b ])) ])))])))])).



top_goal gs_framework decision6 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [(nat arrow nat), (abs f\
	(app forall (tuple [(nat arrow bool), (abs p\
		(app imp (tuple [(app and (tuple [
				(app eq (tuple [(app f (app f (app f (app f (app f x))))), x ])), 
				(app eq (tuple [ (app f (app f (app f x))), x ])) ])) , 
				(app eq (tuple [
				(app p (app f x)),
				(app p x)]))])))])))])))])).

top_goal gs_framework decision7 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [
				(app eq (tuple [x , y ])) ,
				(app eq (tuple [ (app f x), (app f y) ]))])))])))])))])).


top_goal gs_framework decision8 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [
				(app less (tuple [ zero , y ])) ,
				(app leq (tuple [  zero , y ]))])))])))])))])).


top_goal gs_framework decisionSGS1 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(olist nat), (abs l\
	(app forall (tuple [(nat arrow nat), (abs h\
	(app forall (tuple [(nat arrow bool), (abs p\
		(app imp (tuple [(app and (tuple [
(app and (tuple [ (app leq (tuple [ x , y ])) , (app leq (tuple [ y, (app plus (tuple [ x , (app car (app cons (tuple [ zero , l ])))]))]))])) , (app p (app plus (tuple [ (app h x), (app times (tuple [ (app pred zero) , (app h y)]))])))])) , (app p zero)])))])))])))])))])))])).



top_goal gs_framework decisionSGS1a [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(olist nat), (abs l\
	(app forall (tuple [(nat arrow nat), (abs h\
	(app forall (tuple [(nat arrow bool), (abs p\
		(app imp (tuple [(app and (tuple [
(app eq (tuple [ x ,  (app car (app cons (tuple [ y , l ]))) ])) , (app p (app plus (tuple [ (app h x), (app times (tuple [ (app pred zero) , (app h y)]))])))])) , (app p zero)])))])))])))])))])))])).


%top_goal gs_framework decisionSGS1b [] 
%	(app forall (tuple [nat, (abs <lc-0-2>\
%	(app forall (tuple [nat, (abs <lc-0-3>\
%	(app forall (tuple [(olist nat), (abs <lc-0-4>\
%	(app forall (tuple [(nat arrow nat), (abs <lc-0-5>\
%	(app forall (tuple [(nat arrow bool), (abs <lc-0-6>\
%	(app forall (tuple [nat, (abs <lc-0-11>\
%	(app forall (tuple [nat, (abs <lc-0-10>\
%	(app forall (tuple [nat, (abs <lc-0-9>\
%	(app forall (tuple [nat, (abs <lc-0-8>\
%	(app forall (tuple [nat, (abs <lc-0-7>\
%(app or (tuple [
%(app neg ( app leq ( tuple [ <lc-0-2>, <lc-0-2>]))) ,
%     (app neg (app leq (tuple [ <lc-0-2>, (app plus (tuple [ <lc-0-2>, <lc-0-7>]))]))) ,
%	(app neg (app eq (tuple [ app car (app cons (tuple [ <lc-0-7>, <lc-0-4>])),  <lc-0-7>]))), 
%       	(app neg (app eq (tuple [zero ,  <lc-0-7>]))), 
%(app neg (app  <lc-0-6> <lc-0-9>)) , 
%         (app neg (app eq (tuple [ app plus (tuple [ <lc-0-10>, app times (tuple [ (app pred zero), <lc-0-11>])]), <lc-0-9> ]))),
%(app neg (app eq (tuple [ app <lc-0-5> <lc-0-2> , <lc-0-10>]))), 
%           (app neg (app eq (tuple [ app <lc-0-5> <lc-0-2> , <lc-0-11> ]))) ,
%(app <lc-0-6> <lc-0-7>)])))])))])))])))])))])))])))])))])))])))])).


top_goal gs_framework decisionSGS1c [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(olist nat), (abs l\
	(app forall (tuple [(nat arrow nat), (abs h\
	(app forall (tuple [(nat arrow bool), (abs p\
		(app imp (tuple [(app and (tuple [
	(app and (tuple [(app leq (tuple [ x , y ])),(app leq (tuple [ y , x ]))])), (app p (app plus (tuple [ (app h x), (app times (tuple [ (app pred zero) , (app h y)]))])))])) , (app p zero)])))])))])))])))])))])).


top_goal gs_framework decisionSGS2 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [nat, (abs z\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app and (tuple [
			(app eq (tuple [ z , (app f (app plus (tuple [ x , (app times (tuple [ (app pred zero) , y ])) ])))])), 
			(app eq (tuple [ x , (app plus (tuple [ y , z ] ))])) ])) , 
			(app eq (tuple [ (app plus (tuple [ y , (app f (app f z)) ])) , x ])) ])))])))])))])))])).


top_goal gs_framework decisionSGS3 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app and (tuple [
				(app eq (tuple [(app f (app f (app f x))), (app f x) ])), 
				(app eq (tuple [ x , y ])) ])) , 
				(app eq (tuple [
				(app f (app f (app f (app f (app f y))))) , (app f x) ])) ])))])))])))])).


top_goal gs_framework decisionSGS4 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [nat, (abs z\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app and (tuple [
(app eq (tuple [ y, (app f z)])),

(app eq (tuple [ (app plus (tuple [ x, (app times (tuple [ (app pred zero), (app times (tuple [ (app s (app s zero)), y])) ]))])), zero ]))])), 

(app eq (tuple [ (app f (app plus (tuple [ x , (app times (tuple [ (app pred zero), y]))]))),
(app f (app f z))]))])))])))])))])))])).


top_goal gs_framework decisionSGS5 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app and (tuple [
				(app and (tuple [
				(app eq (tuple [(app f x), (app s (app s (app s (app s zero))))])),
				(app eq (tuple [(app f (app plus (tuple [ (app times (tuple [ (app s (app s zero)), y])), (app times (tuple [ (app pred zero), x ]))]))), (app s (app s (app s zero)))]))])), 
				(app eq (tuple [ x, (app f (app plus (tuple [ (app times (tuple [ (app s (app s zero)), x])), (app times (tuple [ (app pred zero), y ]))])))]))])),
				(app neg (app eq (tuple [ (app times (tuple [ (app s (app s (app s (app s zero)))), x ])), (app plus (tuple [ (app times (tuple [ (app s (app s zero)), x ])), (app times (tuple [ (app s (app s zero)), y ])) ]))])))])))])))])))])).


%top_goal gs_framework decisionSGS5 [] 
%	(app forall (tuple [nat, (abs x\
%	(app forall (tuple [nat, (abs y\
%	(app forall (tuple [(nat arrow nat), (abs f\
%
%(app imp (tuple [
%
%(app and (tuple [
%(app eq (tuple [zero , zero ])),
%(app eq (tuple [(app f (app plus (tuple [ x, y ]))), (app s zero)]))])),
%
%(app eq (tuple [ y , zero ]))])))])))])))])).


top_goal gs_framework decisionSGS6 [] 
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app and (tuple [
(app eq (tuple [ (app f (app plus (tuple [ a, (app pred zero)]))), (app plus (tuple [ a, (app s zero)]))])),
(app eq (tuple [ (app plus (tuple [ (app f b), (app s zero)])), (app plus (tuple [ b, (app pred zero)]))]))])),
(app neg (app eq (tuple [ (app plus (tuple [ b , (app s zero)])) , a ])))])))])))])))])).


top_goal gs_framework decisionSGS7 [] 
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app and (tuple [ (app eq (tuple [ (app f a) , a])), (app eq (tuple [ (app plus (tuple [ (app f b), (app s zero)])), b]))])) , (app neg (app eq (tuple [ a , b ])))])))])))])))])).



top_goal gs_framework decisionSGS9 [] 
	(app forall (tuple [nat, (abs l\
	(app forall (tuple [nat, (abs alpha\
	(app forall (tuple [nat, (abs k\
		(app imp (tuple [(app and (tuple [
			(app leq (tuple [ l , (app min alpha) ])),
			(app less (tuple [ zero , k ])) ])), 
			(app neg (app leq (tuple [ (app plus (tuple [ (app max alpha), k ])), l ])))])))])))])))])).


top_goal gs_framework decisionSGS9a [] 
	(app forall (tuple [nat, (abs alpha\
	(app forall (tuple [nat, (abs k\
		(app imp (tuple [
			(app leq (tuple [ (app min alpha), k ])),
			(app leq (tuple [ (app min alpha), (app plus (tuple [ (app max alpha), k ]))]))])))])))])).


top_goal gs_framework decisionSGS9b [] 
	(app forall (tuple [nat, (abs alpha\
		(app leq (tuple [ (app min alpha), (app plus (tuple [ (app max alpha), (app s zero) ]))])))])).



top_goal gs_framework decisionSGS10 [] 
	(app forall (tuple [nat, (abs alpha\
	(app forall (tuple [nat, (abs k\
		(app imp (tuple [(app leq (tuple [ zero , k ])),
			(app leq (tuple [ (app min alpha) , (app plus (tuple [ (app max alpha), k ]))]))])))])))])).


top_goal gs_framework decisionSGS0 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app leq (tuple [ y , (app f x) ])),
			(app leq (tuple [ y, (app s (app f x))]))])))])))])))])).


top_goal gs_framework decisionSGS01 [] 
	(app forall (tuple [nat, (abs x\
	(app forall (tuple [nat, (abs y\
	(app forall (tuple [(nat arrow nat), (abs f\
		(app imp (tuple [(app leq (tuple [ y ,  x ])),
			(app leq (tuple [ y, (app s (x))]))])))])))])))])).



top_goal gs_framework decision_assp [] 
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app forall (tuple [nat, (abs c\
		(app eq (tuple [(app plus (tuple [ (app plus (tuple [ a , b ])), c ])), (app plus (tuple [ a , (app plus (tuple [ b , c ]))])) ])))])))])))])).


top_goal gs_framework decision_nassp [] 
	(app forall (tuple [nat, (abs a\
	(app forall (tuple [nat, (abs b\
	(app forall (tuple [nat, (abs c\
		(app neq (tuple [(app plus (tuple [ (app plus (tuple [ a , b ])), c ])), (app plus (tuple [ a , (app plus (tuple [ b , c ]))])) ])))])))])))])).


% ******************************************************
%
% (S)GS framework
% Theories
%
% ******************************************************


is_otype gs_pia nat [zero] [s].

has_otype gs_pia zero nat.
has_otype gs_pia s (nat arrow nat).
has_otype gs_pia pred (nat arrow nat).
has_otype gs_pia plus ((tuple_type [nat, nat]) arrow nat).
has_otype gs_pia times ((tuple_type [nat, nat]) arrow nat).
has_otype gs_pia leq ((tuple_type [nat, nat]) arrow bool).
has_otype gs_pia less ((tuple_type [nat, nat]) arrow bool).
has_otype gs_pia greater ((tuple_type [nat, nat]) arrow bool).
has_otype gs_pia geq ((tuple_type [nat, nat]) arrow bool).



is_otype gs_objlists (olist nat) [onil] [ cons, cdr ].
has_otype gs_objlists onil (olist nat).
has_otype gs_objlists cons ((tuple_type [nat, (olist nat)]) arrow (olist nat)).
has_otype gs_objlists car ((olist nat) arrow nat).
has_otype gs_objlists cdr ((olist nat) arrow (olist nat)).


% ******************************************************
%
% (S)GS framework
% CNF rule
%
% Based on the idea of sets of normalization rewrite rules
% (see:
% Alan Bundy: The Use of Proof Plans for Normalization
% (in  Essays in Honor of Woody Bledsoe), Kluwer, 1991.
% [Also as DAI Research Paper No. 513]
% and
% Renato Busatto: Proof plans for normalizations
% (PhD thesis, Univ of Edinburgh), 1995
% and
% Alan Bundy: Blue Book Note 1138)
% ******************************************************


gs_prenex_cnf F FF :-
	gs_exhaustivelly_rewrite_with_rules [
		removeiff,
		removeif
		] F F1,
	gs_exhaustivelly_rewrite_with_rules [
		stratify_neg_univquant,
		stratify_neg_exiquant,
		stratify_and_univquant1,
		stratify_and_univquant2,
		stratify_and_exiquant1,
		stratify_and_exiquant2,
		stratify_or_univquant1,
		stratify_or_univquant2,
		stratify_or_exiquant1,
		stratify_or_exiquant2
		] F1 F2,
	gs_exhaustivelly_rewrite_with_rules [
		stratify_neg_and,
		stratify_neg_or
		] F2 F3,
	gs_exhaustivelly_rewrite_with_rules [
		stratify_or_and1,
		stratify_or_and2
		] F3 F4,
	gs_exhaustivelly_rewrite_with_rules [
		thin
		] F4 F5,
	gs_exhaustivelly_rewrite_with_rules [
		thin2,
		thin3
		] F5 FF.



% ***************************************************************
% remove_ removes occurences of function R using
% ***************************************************************


lemma gs_fol removeiff rtol trueP
	( app iff ( tuple [ A , B ]))
	(app and (tuple [(app or ( tuple [ (app neg A) , B ])) , (app or ( tuple [ (app neg B) , A ])) ]  )).

lemma gs_fol removeif rtol trueP
	( app imp( tuple [ A , B ]))
	(app or ( tuple [ (app neg A) , B ])).

% ************************************************************
% thin removes double occurences of function R
% (F2 is free of double occurences of R)
% ************************************************************

lemma gs_fol thin rtol trueP
	( app neg ( app  neg X ))
	X.

lemma gs_fol thin2 rtol trueP
	( app neg ( trueP ))
	falseP.

lemma gs_fol thin3 rtol trueP
	( app neg ( falseP ))
	trueP.



% *************************************************************
% stratify moves connective L1 beneath connective L2 
% *************************************************************

lemma gs_fol stratify_neg_univquant rtol trueP
	(app neg (app forall (tuple [Type , abs (V\ (F V))])))
	(app exists (tuple [Type , (abs (V\ (app neg (F V))))])).

lemma gs_fol stratify_neg_exiquant rtol trueP
	(app neg (app exists (tuple [Type , abs (V\ (F V))])))
	(app forall (tuple [Type , (abs (V\ (app neg (F V))))])).

lemma gs_fol stratify_and_univquant1 rtol trueP 
	(app and (tuple [ (app forall (tuple [Type , abs (V\ (F1 V))])) , F2 ]))
	(app forall (tuple [Type , abs (V\ (app and (tuple [ (F1 V) , F2 ]))) ] )).
% assumes that V does not occurs in F2 ! (i.e. that variables are standardized apart 

lemma gs_fol stratify_and_univquant2 rtol trueP 
	( app and (tuple [ F1 , (app forall (tuple [Type , abs (V\ (F2 V))])) ]))
	(app forall (tuple [Type , abs (V\ (app and (tuple [ F1, (F2 V)]))) ] )).
% assumes that V does not occurs in F1 !

lemma gs_fol stratify_and_exiquant1 rtol trueP 
	( app and (tuple [ (app exists (tuple [Type , abs (V\ (F1 V))])) , F2 ]))
	(app exists (tuple [Type , abs (V\ (app and (tuple [ (F1 V), F2])))] )).
% assumes that V does not occurs in F2 !

lemma gs_fol stratify_and_exiquant2 rtol trueP 
	( app and (tuple [ F1 , (app exists (tuple [Type , abs (V\ (F2 V))])) ]))
	(app exists (tuple [Type , abs (V\ (app and (tuple [ F1 , (F2 V)])))] )).
% assumes that V does not occurs in F1 !


lemma gs_fol stratify_or_univquant1 rtol trueP 
	( app or (tuple [ (app forall (tuple [Type , abs (V\ (F1 V))])) , F2 ]))
	(app forall (tuple [Type , abs (V\ (app or (tuple [ (F1 V) , F2]))) ] )).
% assumes that V does not occurs in F2 !

lemma gs_fol stratify_or_univquant2 rtol trueP 
	( app or (tuple [ F1 , (app forall (tuple [Type , abs (V\ (F2 V))])) ]))
	(app forall (tuple [Type , abs (V\ (app or (tuple [ F1 , (F2 V)]))) ] )).
% assumes that V does not occurs in F1 !

lemma gs_fol stratify_or_exiquant1 rtol trueP 
	( app or (tuple [ (app exists (tuple [Type , abs (V\ (F1 V))])) , F2 ]))
	(app exists (tuple [Type , abs (V\ (app or (tuple [ (F1 V) , F2])))] )).
% assumes that V does not occurs in F2 !

lemma gs_fol stratify_or_exiquant2 rtol trueP 
	( app or (tuple [ F1 , (app exists (tuple [Type , abs (V\ (F2 V))])) ]))
	(app exists (tuple [Type , abs (V\ (app or (tuple [ F1 , (F2 V)]))) ])).
% assumes that V does not occurs in F1 !

lemma gs_fol stratify_neg_and rtol trueP
	( app neg (app and (tuple [ F1 , F2 ])))
	(app or (tuple [ (app neg F1) , (app neg F2) ])).

lemma gs_fol stratify_neg_or rtol trueP
	( app neg (app or (tuple [ F1 , F2 ])))
	(app and (tuple [ (app neg F1) , (app neg F2) ])).

lemma gs_fol stratify_or_and1 rtol trueP
	( app or (tuple [ F1 , (app and (tuple [ F2 , F3 ])) ]))
	( app and (tuple [ (app or (tuple [F1 , F2])), (app or (tuple [F1 , F3])) ])).

lemma gs_fol stratify_or_and2 rtol trueP
	( app or (tuple [ (app and (tuple [ F2 , F3 ])) , F1 ]))
	( app and (tuple [ (app or (tuple [F2 , F1])), (app or (tuple [F3 , F1])) ])).

lemma gs_fol stratify_and_or1 rtol trueP
	( app and (tuple [ F1 , (app or (tuple [ F2 , F3 ])) ]))
	( app or (tuple [ (app and (tuple [F1 , F2])), (app and (tuple [F1 , F3])) ])).

lemma gs_fol stratify_and_or2 rtol trueP
	( app and (tuple [ (app or (tuple [ F2 , F3 ])) , F1 ]))
	( app or (tuple [ (app and (tuple [F2 , F1])), (app and (tuple [F3 , F1])) ])).




% ******************************************************
%
% (S)GS framework
% Simplification rule
%
% Recall that GS framework is formulated as proof-refutation system
% so all rules here are dual to the corresponding rules in GS paper
%
% ******************************************************



gs_simplify Theories F FF :- 
	gs_disjunction_to_list_of_literals F L,
	gs_simpl Theories L LL,
	gs_list_of_literals_to_disjunction LL FF.



% there are two forms of simplification:
% (1) gs_simpl nil L LL  - no theory specific simplification
% (2) gs_simpl TL  L LL - with theory specific simplifications (TL is a list of theories)


% there are 9 general simplification rules

% rule 1: empty list -> false goal 
gs_simpl nil nil [ falseP ] :- !.

% rule 2: delete multiple occurences of a literal
gs_simpl nil L LL :-
	gs_member A L,
	gs_number_of_literals_in_list A L N, N > 1, !,
	gs_delete_from_list A L L1,
	append L1 [ A ] L2,     % we want to keep only one occurence of A
	gs_simpl nil L2 LL.

% rule 3: detected true goal - goal includes both a literal and its negation
gs_simpl nil L [ trueP ] :-
	gs_member A L,
	gs_member (app neg A) L, !.

% rule 4: detected true goal - goal includes true literal
gs_simpl nil L [ trueP ] :-
    	not (L = [ trueP ] ),
	gs_member trueP L, !.

% rule 5: eliminate false goals
gs_simpl nil L LL :-
	gs_member falseP L, !,
	gs_delete_from_list falseP L L1,
	gs_simpl nil L1 LL.

% rule 6: eliminates trivial disequalities
gs_simpl nil L LL :-
	gs_member (app neg (app eq (tuple [ A , A ]))) L, !,
	gs_delete_from_list (app neg (app eq (tuple [ A , A ]))) L L1,
	gs_simpl nil L1 LL.

% rule 7: detected true goal - there is trivial par of inequality
gs_simpl nil L [ trueP ] :-
	gs_member (app eq (tuple [ A , A ])) L, !.

% rule 8: eliminates disequalities neg(x=y) where x does not appear elsewhere
gs_simpl nil L LL :-
	gs_member (app neg (app eq (tuple [ X , Y ] ))) L,
	gs_delete_from_list (app neg (app eq (tuple [ X , Y ] ))) L L1,
	obj_atom X,
	gs_number_of_occs_in_term X Y 0,
	gs_number_of_occs_in_list X L1 0, !,
	gs_simpl nil L1 LL.
gs_simpl nil L LL :-
	gs_member (app neg (app eq (tuple [ Y , X ] ))) L,
	gs_delete_from_list (app eq (tuple [ Y , X ] )) L L1,
	obj_atom Y,
	gs_number_of_occs_in_term Y X 0,
	gs_number_of_occs_in_list Y L1 0, !,
	gs_simpl nil L1 LL.

gs_simpl nil L L.

gs_simpl (Theory::TheoryList) L LL :-
	gs_simpl_theory Theory L L1,
	gs_simpl TheoryList L1 LL.

%gs_simpl_theory _ L L.




% ******************************************************
%
% (S)GS framework
%
% Grammars module and support for the absp rule
%
% ******************************************************

gs_abspplus Theories Hyp F FF AbsVars :-
	gs_disjunction_to_list_of_literals F L,
	gs_abspplus_ Theories Hyp L L1 A,
	gs_remove_duplicates L L1 LL A AbsVars,
	gs_list_of_literals_to_disjunction LL FF.

gs_abspplus_ _Theories _Hyp nil nil nil.
gs_abspplus_ Theories Hyp (A::L) (AA::LL) AbsVars:-
	gs_abs_one_literal Theories Hyp A AA E AV1,
	gs_abspplus_ Theories Hyp L L1 AV2,
	append E L1 LL,
	append AV1 AV2 AbsVars.

% deleted 02.08.2002
% 
%gs_remove_duplicates L L1 LL A AA :-
%	gs_get_two_members (app neg (app eq (tuple [ Term , V1 ]))) (app neg (app eq (tuple [ Term , V2 ]))) L1,
%	not (gs_same V1 V2), !,
%	gs_delete_from_list (app neg (app eq (tuple [ Term , V2 ]))) L1 La,
%	gs_member [ Var , Type ] A,
%	gs_same Var V2,
%	gs_delete_from_list [ V2 , Type ] A A1,
%	gs_replace_all_in_list V2 V1 La L2,
%	gs_remove_duplicates L L2 LL A1 AA.
gs_remove_duplicates _ L L A A.


gs_abs_one_literal Theories Hyp A A nil nil :-
	gs_member Theory Theories,
	gs_is_T_literal Hyp Theory bool A, !.
gs_abs_one_literal Theories Hyp (app neg X) (app neg XX) E AV:-
	!,
	gs_abs_one_literal Theories Hyp X XX E AV.

gs_abs_one_literal Theories Hyp (app eq (tuple [ X , Y ] )) (app eq (tuple [ X , Y ] )) E nil :-
	obj_atom X,
	obj_atom Y,
	gs_var X,
	gs_var Y, !.

gs_abs_one_literal Theories Hyp (app eq (tuple [ (app X Z), Y ] )) (app eq (tuple [ XX, YY ] )) E AV :-
	gs_member Theory Theories,
	gs_has_otype Theory X ((tuple_type TT) arrow Type),
	!,
	gs_abs_list_of_terms Theory Theories Hyp [ (app X Z), Y ] [ Type , Type ] [ XX , YY] E AV.
gs_abs_one_literal Theories Hyp (app eq (tuple [ Y, (app X Z) ] )) (app eq (tuple [ YY, XX ] )) E AV :-
	gs_member Theory Theories,
	gs_has_otype Theory X ((tuple_type TT) arrow Type),
	!,
	gs_abs_list_of_terms Theory Theories Hyp [ Y, (app X Z) ] [ Type , Type ] [ YY , XX ] E AV.
gs_abs_one_literal Theories Hyp (app eq (tuple [ X , Y ] )) (app eq (tuple [ XX , YY ] )) E AV :-
	gs_member Theory Theories,
	not (obj_atom X),
	not (gs_var X),
	gs_is_T_term Hyp Theory Type X,
	!,
	gs_abs_list_of_terms Theory Theories Hyp [ X, Y ] [ Type , Type ] [ XX , YY] E AV.
gs_abs_one_literal Theories Hyp (app eq (tuple [ X , Y ] )) (app eq (tuple [ XX , YY ] )) E AV :-
	gs_member Theory Theories,
	not (obj_atom Y),
	not (gs_var Y),
	gs_is_T_term Hyp Theory Type Y,
	!,
	gs_abs_list_of_terms Theory Theories Hyp [ X, Y ] [ Type , Type ] [ XX , YY] E AV.
gs_abs_one_literal Theories Hyp (app eq (tuple [ X , Y ] )) (app eq (tuple [ XX , YY ] )) E AV :-
	gs_member gs_pure_equality Theories,
	gs_abs_list_of_terms gs_pure_equality Theories Hyp [ X, Y ] [ Type , Type ] [ XX , YY] E AV.

gs_abs_one_literal Theories Hyp (app X (tuple Y)) (app X (tuple YY)) E AV:-
	gs_member gs_pure_equality Theories,
	not (X = eq),
	(gs_member (otype_of X ((tuple_type TT) arrow bool)) Hyp),!,
	gs_abs_list_of_terms gs_pure_equality Theories Hyp Y TT YY E AV.

gs_abs_one_literal Theories Hyp (app X Y) (app X YY) E AV:-
	gs_member gs_pure_equality Theories,
	not (X = eq),
	(gs_member (otype_of X (TT arrow bool)) Hyp),!,
	gs_abs_one_term gs_pure_equality Theories Hyp Y TT YY E AV.
gs_abs_one_literal Theories Hyp (app X (tuple Y)) (app X (tuple YY)) E AV:-
	gs_member Theory Theories,
	not (X = eq),
	gs_has_otype Theory X ((tuple_type TT) arrow bool),!,
	gs_abs_list_of_terms Theory Theories Hyp Y TT YY E AV.


gs_abs_one_literal Theories Hyp (app X Y) (app X YY) E AV :-
	gs_member gs_pure_equality Theories,
	not (X = eq),
	!,
	(gs_member (otype_of X (TT arrow bool)) Hyp),!,
	gs_abs_one_term gs_pure_equality Theories Hyp Y TT YY E AV.
gs_abs_one_literal Theories Hyp (app X Y) (app X YY) E AV :-
	gs_member Theory Theories,
	not (X = eq),
	!,
	gs_has_otype Theory X (TT arrow bool),
	gs_abs_one_term Theory Theories Hyp Y TT YY E AV.


gs_abs_one_term Theory _Theories Hyp X Type X nil nil :-
	gs_is_T_term Hyp Theory Type X, !.

gs_abs_one_term Theory Theories Hyp (app X (tuple Y)) Type (app X (tuple YY)) E AV :-
	Theory = gs_pure_equality,
	gs_member Theory Theories,
	gs_member (otype_of X (tuple_type TT arrow Type)) Hyp,
	!,
	gs_abs_list_of_terms Theory Theories Hyp Y TT YY E AV.
gs_abs_one_term Theory Theories Hyp (app X (tuple Y)) Type (app X (tuple YY)) E AV :-
	gs_has_otype Theory X (tuple_type TT arrow Type),
	!,
	gs_abs_list_of_terms Theory Theories Hyp Y TT YY E AV.
gs_abs_one_term Theory Theories Hyp (app X Y) Type (app X YY) E AV :-
	gs_has_otype Theory X (TT arrow Type),
	!,
	gs_abs_one_term Theory Theories Hyp Y TT YY E AV.
gs_abs_one_term Theory Theories Hyp (app X Y) Type (app X YY) E AV :-
	Theory = gs_pure_equality,
	gs_member (otype_of X (TT arrow Type)) Hyp,
	!,
	gs_abs_one_term Theory Theories Hyp Y TT YY E AV.

gs_abs_one_term Theory Theories Hyp (app X (tuple Y)) Type NewVar E ([ NewVar , Type ]::AV) :-
	gs_member Theory1 Theories,
	Theory1 = gs_pure_equality,
	gs_member (otype_of X (tuple_type TT arrow Type)) Hyp,
	!,
	gs_abs_list_of_terms Theory1 Theories Hyp Y TT YY E1 AV,
	gs_getnewvarname AV NewVar,
	append [ (app neg (app eq (tuple [ (app X (tuple YY)), NewVar ])))] E1 E.

gs_abs_one_term Theory Theories Hyp (app X (tuple Y)) Type NewVar E ([ NewVar , Type ]::AV) :-
	gs_member Theory1 Theories,
	gs_has_otype Theory1 X (tuple_type TT arrow Type),
	!,
	gs_abs_list_of_terms Theory1 Theories Hyp Y TT YY E1 AV,
	gs_getnewvarname AV NewVar,
	append [ (app neg (app eq (tuple [ (app X (tuple YY)), NewVar ])))] E1 E.

gs_abs_one_term Theory Theories Hyp (app X Y) Type NewVar E ([ NewVar , Type]::AV) :-
	gs_member Theory1 Theories,
	gs_has_otype Theory1 X (TT arrow Type),
	!,
	gs_abs_one_term Theory1 Theories Hyp Y TT YY E1 AV,
	gs_getnewvarname AV NewVar,
	append [ (app neg (app eq (tuple [ (app X YY), NewVar ])))] E1 E.

gs_abs_one_term Theory Theories Hyp (app X Y) Type NewVar E ([ NewVar , Type]::AV) :-
	gs_member Theory1 Theories,
	Theory1 = gs_pure_equality,
	gs_member (otype_of X (TT arrow Type)) Hyp,
	!,
	gs_abs_one_term Theory1 Theories Hyp Y TT YY E1 AV,
	gs_getnewvarname AV NewVar,
	append [ (app neg (app eq (tuple [ (app X YY), NewVar ])))] E1 E.

gs_abs_one_term Theory Theories Hyp X Type NewVar [ (app neg (app eq (tuple [ X, NewVar ])))] ([ NewVar , Type ]::nil) :-
	gs_getnewvarname AV NewVar,
	gs_member Theory1 Theories,
	Theory1 = gs_pure_equality,
	gs_member (otype_of X Type) Hyp.

gs_abs_one_term Theory Theories Hyp X Type NewVar [ (app neg (app eq (tuple [ X, NewVar ])))] ([ NewVar , Type ]::nil) :-
	gs_getnewvarname AV NewVar,
	gs_member Theory1 Theories,
	gs_has_otype Theory1 X Type.

gs_abs_list_of_terms _Theory _Theories Hyp nil nil nil nil nil :- !.
gs_abs_list_of_terms Theory Theories Hyp (X::Y) (Type::Types) (XX::YY) E AV :-
	gs_abs_one_term Theory Theories Hyp X Type XX E1 AV1,
	!,
	gs_abs_list_of_terms Theory Theories Hyp Y Types YY E2 AV2,
	append E1 E2 E,
	append AV1 AV2 AV.

local gs_getnewvarname ((list X) -> Y -> o).

gs_getnewvarname _ NewVar.



% this predicate checks whether literal Literal belongs to the
% theory Theory and has the type Type
gs_is_T_literal Hyp Theory bool trueP :- !.
gs_is_T_literal Hyp Theory bool falseP :- !.

gs_is_T_literal Hyp Theory bool (app neg L) :-
	!,
	gs_is_T_literal Hyp Theory bool L.
gs_is_T_literal Hyp gs_pure_equality bool (app eq (tuple Y)) :-
	gs_are_T_terms Hyp gs_pure_equality [ T , T ] Y, !.

gs_is_T_literal Hyp Theory bool (app eq (tuple Y)) :-
	gs_are_T_terms Hyp Theory [ T , T ] Y, !.


gs_is_T_literal Hyp gs_pure_equality bool (app X (tuple Y)) :-
	gs_member (otype_of X (tuple_type TT arrow bool)) Hyp,
	gs_are_T_terms Hyp gs_pure_equality TT Y, !.
gs_is_T_literal Hyp gs_pure_equality bool (app X Y) :-
	gs_member (otype_of X (Type1 arrow bool)) Hyp,
	gs_is_T_term Hyp gs_pure_equality Type1 Y, !.

gs_is_T_literal Hyp Theory bool (app X (tuple Y)) :-
	gs_has_otype Theory X (tuple_type TT arrow bool),
	gs_are_T_terms Hyp Theory TT Y, !.
gs_is_T_literal Hyp Theory bool (app X Y):-
	gs_has_otype Theory X (Type1 arrow bool),
	gs_is_T_term Hyp Theory Type1 Y.


% this predicate checks whether term Term belongs to the
% theory Theory and has the type Type

gs_is_T_term Hyp Theory Type Term :- gs_has_otype Theory Term Type, !.
gs_is_T_term Hyp Theory Type (app X (tuple Y)) :-
	gs_has_otype Theory X (tuple_type TT arrow Type),
	gs_are_T_terms Hyp Theory TT Y,!.
gs_is_T_term Hyp gs_pure_equality Type (app X (tuple Y)) :-
	gs_member (otype_of X (tuple_type TT arrow Type)) Hyp,
	gs_are_T_terms Hyp Theory TT Y,!.
gs_is_T_term Hyp Theory Type (app X Y) :-
	gs_has_otype Theory X (Type1 arrow Type),
	gs_is_T_term Hyp Theory Type1 Y,!.
gs_is_T_term Hyp gs_pure_equality Type (app X Y) :-
	gs_member (otype_of X (Type1 arrow Type)) Hyp,
	gs_is_T_term Hyp gs_pure_equality Type1 Y,!.
gs_is_T_term Hyp Theory Type X :- gs_var X.



gs_are_T_terms Hyp _ nil nil.
gs_are_T_terms Hyp Theory (Type::TT) (Y::YY) :-
	gs_is_T_term Hyp Theory Type Y,
	gs_are_T_terms Hyp Theory TT YY.
	


gs_has_otype Theory X Type :- has_otype Theory X Type, !.
gs_has_otype Theory X Type :- has_otype Theory1 X Type, !, fail.
gs_has_otype Theory X Type :- (not (Type = (_ arrow _))), obj_atom X.

gs_var X :- gs_has_otype Theory X Type, !, fail.
gs_var X :- obj_atom X.




gs_list_of_T_literals Hyp Theory nil nil.
gs_list_of_T_literals Hyp Theory (A::L) (A::LL) :-
	gs_is_T_literal Hyp Theory bool A,
	!,
	gs_list_of_T_literals Hyp Theory L LL.
gs_list_of_T_literals Hyp Theory (A::L) LL :-
	gs_list_of_T_literals Hyp Theory L LL.






% ******************************************************
%
% (S)GS framework
%
% Replace rules
%
% ******************************************************


gs_repl F FF :-
	gs_disjunction_to_list_of_literals F L,
	gs_repl_ L LL,
	gs_list_of_literals_to_disjunction LL FF.


gs_repl_ L LL :-
	gs_repl_one L L1, !,
	gs_repl_ L1 LL.
gs_repl_ L L.


gs_repl_one L LL :-
	gs_member (app neg ( app eq (tuple [A , B]))) L,
	obj_atom A,
	gs_var A,
	not ( gs_occurs A B ),
	!,
	gs_delete_from_list (app neg (app eq (tuple [A , B]))) L L1,
	gs_replace_all_in_list A B L1 LL.


gs_repl_one L LL :-
	gs_member (app neg (app eq (tuple [B , A]))) L,
	obj_atom B,
	gs_var B,
	not ( gs_occurs A B ),
	!,
	gs_delete_from_list (app neg (app eq (tuple [B , A]))) L L1,
	gs_replace_all_in_list A B L1 LL.
%printstdout LL.

% ----------------------------------------
% repl=  rule


gs_repl_eq F FF :-
	gs_disjunction_to_list_of_literals F L,
	gs_repl_eq_ L LL,
	gs_list_of_literals_to_disjunction LL FF.


gs_repl_eq_ L LL :-
	gs_repl_eq_one L L1, !,
	gs_repl_eq_ L1 LL.
gs_repl_eq_ L L.

gs_repl_eq_one L LL :-
	gs_member (app neg (app eq (tuple [A , B]))) L,
	obj_atom A,
 	obj_atom B,
	gs_var A,
	gs_var B,
	!,
	gs_delete_from_list (app neg (app eq (tuple [A , B]))) L L1,
	gs_replace_all_in_list A B L1 LL.



% ******************************************************
%
%  (S)GS framework
%
%  Lemma invoking rule
%  Note that reduction ordering is (still) not available in LambdaClam,
%  so termination (when using this rule) is not ensured
%
% ******************************************************

type xx osyn.

gs_lemma Theories Hyp F FF AbsVars :-
	gs_disjunction_to_list_of_literals F L,
	gs_lemma_ Theories Hyp L LL AbsVars,
	gs_list_of_literals_to_disjunction LL FF.

/*
gs_lemma_ Theories Hyp L LL nil :-
	member D L,
%	(not (D = (app eq _))),
	not ( gs_member Theory Theories, gs_is_T_literal Hyp Theory bool D),
	gs_is_T_literal Hyp gs_lemmas bool D,
	lemma gs_lemmas Name rtol Conditions LH RH,
	LH = D,
	!,
	append L [ (app and (tuple [ Conditions , RH ])) ] L1,
	gs_replace_all_in_list LH falseP L1 LL.
*/


gs_lemma_ Theories Hyp L LL AbsVars :-
	(
	 ( gs_member (app neg (app _ (tuple [ A , B ]))) L );
         ( gs_member (app neg (app _ (tuple [ B , A ]))) L )),
	not ( A = (app neg _)),
	gs_has_otype gs_lemmas AA (_ arrow Type),
	lemma gs_lemmas Name rtol Conditions (app O (tuple [ LHa , LHb ])) trueP,
	LHa = A,
	printstdout "Using lemma: ",
	printstdout Name,
	!,
	append L [ (app and (tuple [ Conditions , (app neg (app O (tuple [ LHa , LHb ] )) ) ] ) ) ] L1,
	AbsVars = ([ xx , Type ]::nil),
	gs_replace_all_in_list A xx L1 LL.


gs_lemma_ Theories Hyp L LL ([ xx , Type ]::nil) :-
	(
	 ( gs_member (app _ (tuple [ A , B ])) L );
         ( gs_member (app _ (tuple [ B , A ])) L )),
	not ( A = (app neg _)),
	gs_has_otype gs_lemmas AA (_ arrow Type),
	lemma gs_lemmas Name rtol Conditions (app O (tuple [ LHa , LHb ])) trueP,
	LHa = A,
	printstdout "Using lemma: ",
	printstdout Name,
	!,
	append L [ (app and (tuple [ Conditions , (app neg (app O (tuple [ LHa , LHb ] )) ) ] ) ) ] L1,
	gs_replace_all_in_list LHa xx L1 LL.


gs_lemma_ Theories Hyp L LL ([ xx , Type ]::nil) :-
	(
	 ( gs_member (app neg (app _ (tuple [ A , B ]))) L );
         ( gs_member (app neg (app _ (tuple [ B , A ]))) L )),
	not ( A = (app neg _)),
	gs_has_otype gs_lemmas AA (_ arrow Type),
	printstdout "Using 0 lemmas (generalisation)",
	!,
	gs_replace_all_in_list A xx L LL.



/*
gs_lemma_ Theories Hyp L LL ([ X , Type ]::nil) :-
	(
	 ( gs_member (app neg (app _ (tuple [ (app A Ar) , B ]))) L ) ;
         ( gs_member (app neg (app _ (tuple [ B , (app A Ar) ]))) L ) ),
	gs_has_otype gs_lemmas A T,
printstdout A,
%	gs_member Theory Theories ),
	gs_has_otype Th A (_ arrow Type),
printstdout (_ arrow Type),
	lemma gs_lemmas Name rtol Conditions (app O (tuple [ La, Lb ])) RH,
	La = (app A Ar),
	!,
	append L [ (app and (tuple [ Conditions , (app neg (app eq (tuple [ (app O (tuple [ La, Lb])) , RH ] )) ) ] ) ) ] L1,
	gs_replace_all_in_list LH X L1 LL.

*/

gs_lemma_ Theories Hyp L LL nil :-
	member D L,
	(not (D = (app eq _))),
	not ( gs_member Theory Theories, gs_is_T_literal Hyp Theory bool D),
	!,
	gs_replace_all_in_list D falseP L LL.

/*
gs_lemma_ Theories Hyp L LL ([ X , Type ]::nil) :-
	( (
            ( gs_member (app eq (tuple [ (app A B) , C ])) L ) ;
            ( gs_member (app eq (tuple [ C , (app A B) ])) L )
          ) ,
	gs_has_otype Theory A _ ,
	not ( gs_member Theory Theories ),
	not ( Theory = constructive_logic )
	),
	gs_member (otype_of A (_ arrow Type) ) Hyp ,
	% in this case, we deal with "non-interpreted" function
	% which is not part of any available theory and hence
	% its type must be then in Hypothesis
	!,
	gs_replace_all_in_list (app A B) X L LL.
*/




% **************************************************************
%
%  (S)GS framework
%
%  Miscellaneous 
%
% **************************************************************


gs_member A (A::H).
gs_member A (B::H) :- gs_member A H.

gs_diff L (A::T) LL :-
	gs_delete_from_list A L L1,
	gs_diff L1 T LL.
gs_diff L nil L.

%gs_get_two_members X Y (X::Y::nil).
gs_get_two_members X Y (X::L) :- gs_member Y L.
gs_get_two_members X Y (H::L) :- gs_get_two_members X Y L.


gs_exhaustivelly_rewrite_with_rules L F FF :-
	gs_rewrite_with_rules L _ F F1 trueP, !,
	gs_exhaustivelly_rewrite_with_rules L F1 FF.
gs_exhaustivelly_rewrite_with_rules L F F.

gs_exhaustivelly_rewrite_list_with_rules Rules nil nil.
gs_exhaustivelly_rewrite_list_with_rules Rules (A::L) (AA::LL) :-
	gs_exhaustivelly_rewrite_with_rules Rules A AA,
	gs_exhaustivelly_rewrite_list_with_rules Rules L LL.

gs_rewrite_with_rules L _ (app neg Y) (app neg YY) trueP :-
	!,
	gs_rewrite_with_rules L _ Y YY trueP.
gs_rewrite_with_rules L _ F FF trueP :-
	rewrite_with_rules L _ F FF trueP.

gs_occurs A A :- !.  
gs_occurs A (app B C):- (gs_occurs A B) ; (gs_occurs A C).
gs_occurs A (tuple X):- gs_occurs_in_list A X.

gs_occurs_in_list A (H::L) :- gs_occurs A H, !.
gs_occurs_in_list A (H::L) :- gs_occurs_in_list A L.

gs_number_of_occs_in_list A nil 0 :- ! .
gs_number_of_occs_in_list A (H::R) N :-
	gs_number_of_occs_in_term A H N1,
	gs_number_of_occs_in_list A R N2,
	N is N1 + N2.

gs_number_of_occs_in_term A AA 1 :- not ( not (A = AA)), !.
gs_number_of_occs_in_term A (app B C) N :-
	gs_number_of_occs_in_term A C N2,
	gs_number_of_occs_in_term A B N1,
	N is N1 + N2.
gs_number_of_occs_in_term A (tuple T) N :-
	gs_number_of_occs_in_list A T N.
gs_number_of_occs_in_term A B 0 :-
	not (B = A),
	not (B = (app _ _)),
	not (B = (tuple _)).

type  dummya  osyn.
type  dummyb  osyn.

gs_same X Y :-
	gs_free_var X,
	gs_free_var Y, !,
	not ( X = dummya , Y = dummyb ).
gs_same X Y :-
	gs_free_var X,!, fail.
gs_same X Y :-
	gs_free_var Y, !, fail.
gs_same (app X Y) (app X YY) :- !,
	gs_same Y YY.
gs_same (tuple X) (tuple XX) :-
	!,
	gs_same X XX.

gs_same (X::Y) (XX::YY) :-
	!,
	gs_same X XX,
	gs_same Y YY.
gs_same X Y :-
	X = Y.


gs_free_var  X :-
        not ( not ( X = dummya ) ).


gs_delete_from_list _ nil nil :- !.
gs_delete_from_list A (AA::R) RR :-
	gs_same A AA, !,
	gs_delete_from_list A R RR.
gs_delete_from_list A (B::R) (B::RR) :-	!,
	gs_delete_from_list A R RR.

gs_number_of_literals_in_list _ nil 0.
gs_number_of_literals_in_list A (A::L) N :- !,
	gs_number_of_literals_in_list A L N1,
	N is N1 + 1.
gs_number_of_literals_in_list A (_::L) N :- !,
	gs_number_of_literals_in_list A L N.


gs_replace_all_in_list _ _ nil nil :- !.
gs_replace_all_in_list A B (F::L) (FF::LL) :-
	gs_replace_all A B F FF,
	gs_replace_all_in_list A B L LL.

% NB: does not work properly if the third argument has meta variables!

%gs_replace_all A B A B :- !.

/*
gs_replace_all (A:osyn) B (D:osyn) C :- printstdout "1!!!!!!",
printstdout A,
printstdout D,
(A = D), printstdout "a", ( C = B ), printstdout C, !.
*/

gs_replace_all A B C B :-
%	gs_free_var C,  02.08.2002
	gs_same A C, !.
gs_replace_all A B C C :- gs_free_var C, !.
gs_replace_all A B (app X Tuple) (app XX (tuple TT)) :- 
        not (gs_free_var Tuple), 
	Tuple = (tuple T), !,
	gs_replace_all A B X XX,
	gs_replace_all_in_list A B T TT.
gs_replace_all A B (app X Y) (app XX YY) :- !,
	gs_replace_all A B X XX,
	gs_replace_all A B Y YY.
gs_replace_all A B AA B :- 
	gs_same A AA, !.
gs_replace_all A B C C :- !.



gs_disjunction_to_list_of_literals (app or (tuple([A, B]))) L :-
	!,
	gs_disjunction_to_list_of_literals A L1,
	gs_disjunction_to_list_of_literals B L2,
	append L1 L2 L.
gs_disjunction_to_list_of_literals A [ A ].

gs_list_of_literals_to_disjunction nil falseP :- !.
gs_list_of_literals_to_disjunction (H::nil) H :- !.
gs_list_of_literals_to_disjunction (H::L) (app or (tuple [ H , F1 ])) :- !,
	gs_list_of_literals_to_disjunction L F1.


gs_convert_list_to_oyster_syntax nil nil.
gs_convert_list_to_oyster_syntax (A::L) (AA::LL) :-
	gs_convert_to_oyster_syntax A AA,
	gs_convert_list_to_oyster_syntax L LL.

gs_get_list_lclam_term_from_string nil nil.
gs_get_list_lclam_term_from_string (A::L) (AA::LL) :-
	gs_get_lclam_term_from_string A AA,
	gs_get_list_lclam_term_from_string L LL.


gs_convert_to_oyster_syntax S T :-
	gs_convert_to_oyster_syntax_ S T.
%	T is (T1 ^ ".").


gs_convert_to_oyster_syntax_ (falseP) "void" :- !.
gs_convert_to_oyster_syntax_ (trueP) "{true}" :- !.
gs_convert_to_oyster_syntax_ (zero) "0" :- !.
gs_convert_to_oyster_syntax_ (app neg F) FString :-
	!,
	gs_convert_to_oyster_syntax_ F FS,
	FString is ( ( "((" ^ FS ) ^ ")=>void)" ).
gs_convert_to_oyster_syntax_ (app eq (tuple[ X , Y ])) FString :-
	!,
	gs_convert_to_oyster_syntax_ X XX,
	gs_convert_to_oyster_syntax_ Y YY,
	FString is ( "(" ^ ( ( ( XX ^ "=") ^ YY ) ^ " in generic_type)" ) ).
gs_convert_to_oyster_syntax_ (app X (tuple [ Y , Z ])) FString :-
	!,
	gs_convert_to_oyster_syntax_ X XX,
	gs_convert_to_oyster_syntax_ Y YY,
	gs_convert_to_oyster_syntax_ Z ZZ,
	FString is ( ( ( ( ( XX ^ "(" ) ^ YY ) ^ "," ) ^ ZZ ) ^ ")" ).
gs_convert_to_oyster_syntax_ (app X Y) FString :-
	!,
	gs_convert_to_oyster_syntax_ X XX,
	gs_convert_to_oyster_syntax_ Y YY,
	FString is ( ( (  XX ^ "(" ) ^ YY ) ^ ")" ).
gs_convert_to_oyster_syntax_ X XX :- term_to_string X XX.

gs_get_lclam_term_from_string String Term :- gs_string_to_term String Term.


gs_make_one_string_conj L S :-
	gs_make_one_string_conj_ L S1,
	S is (S1 ^ ".").

gs_make_one_string_conj_ nil "".
gs_make_one_string_conj_ (X::L) String :-
	not(L = nil),
	!,
	gs_make_one_string_conj_ L S,
	String is ((( ("(" ^ X) ^ "#") ^ S) ^ ")" ).
gs_make_one_string_conj_ (X::nil) String :- !,
%	gs_make_one_string_conj_ L S,
	String is ( ("(" ^ X) ^ ")" ).


gs_make_one_string_disj L S :-
	gs_make_one_string_disj_ L S1,
	S is (S1 ^ ".").

gs_make_one_string_disj_ nil "".
gs_make_one_string_disj_ (X::L) String :-
	not(L = nil),
	!,
	gs_make_one_string_disj_ L S,
	String is ((( ("(" ^ X) ^ "\\") ^ S) ^ ")" ).
gs_make_one_string_disj_ (X::nil) String :- !,
%	gs_make_one_string_disj_ L S,
	String is ( ("(" ^ X) ^ ")" ).


gs_negate_all_literals nil nil.
gs_negate_all_literals ((falseP)::L) ((trueP)::LL) :- !.
gs_negate_all_literals ((trueP)::L) ((falseP)::LL) :- !.
gs_negate_all_literals ((app neg X)::L) (X::LL) :-
	!,
	gs_negate_all_literals L LL.
gs_negate_all_literals (X::L) ((app neg X)::LL) :-
	!,
	gs_negate_all_literals L LL.





% **************************************************************
%
%  (S)GS framework
%
%  Lemmas
%
% **************************************************************


has_otype gs_lemmas min (nat arrow nat).
has_otype gs_lemmas max (nat arrow nat).

lemma gs_lemmas min_max rtol trueP
	( app leq (tuple [ (app min X) , (app max X)]))
	( trueP ).

has_otype gs_lemmas minpair ((tuple_type [nat, nat]) arrow nat).
has_otype gs_lemmas maxpair ((tuple_type [nat, nat]) arrow nat).

/*
lemma gs_lemmas minmaxpairs rtol (app eq (tuple [ (app maxpair (tuple [ X , Y ])) , X ]))
	( (app minpair (tuple [ X , Y ])) )
	( Y ).
*/

lemma gs_lemmas minmaxpairs rtol (app eq (tuple [ (app maxpair (tuple [ X , Y ])) , X ]))
	( (app eq (tuple [ (app minpair (tuple [ X , Y ])) , Y ])) )
	( trueP ).


lemma gs_lemmas min_max rtol trueP
	( app leq (tuple [ (app min X) , (app max X)]))
	( trueP ).



lemma gs_objlists ax1 rtol trueP
	( app cons (tuple [ (app car X), (app cdr X)]))
	( X ).

lemma gs_objlists ax2 rtol trueP
	( app car (app cons (tuple [ X , Y ])))
	( X ).

lemma gs_objlists ax3 rtol trueP
	( app cdr (app cons (tuple [ X , Y ])))
	( Y ).


 



% ******************************************************
%
%  (S)GS framework
%
%  Entailment rule
%
% ******************************************************



gs_entail_no Theories Hyp F (app neg (app eq (tuple [ X, Y ]))) :-
	gs_disjunction_to_list_of_literals F L,
	gs_member Theory Theories,
	gs_list_of_T_literals Hyp Theory L L1,
	not (L1 = nil),
%	gs_member (otype_of X (Type) ) Hyp ,
%	not (Type = (_ arrow _)),
%	gs_member (otype_of Y (Type) ) Hyp ,
	gs_get_two_members (otype_of X (Type) ) (otype_of Y (Type) ) Hyp,
  	not (Type = (_ arrow _)),
	not (X = Y),
	not (gs_member (app neg (app eq (tuple [ X, Y ]))) L1),
	not (gs_member (app neg (app eq (tuple [ Y, X ]))) L1),
	gs_occurs_in_list X L1,
	gs_occurs_in_list Y L1, 
	append L1 [(app eq (tuple [ X , Y ]))] L2,
printstdout "Nelson/Oppen entailment attempt:",
%printstdout L2,
printstdout X,
printstdout Y,
	gs_valid Theory L2, !,
printstdout "-------> implicit disequality in theory --------->",
printstdout Theory,
printstdout X,
printstdout Y,
	gs_list_of_literals_to_disjunction L2 FF.


gs_entail_shostak Hyp Theories F FF :- 
	gs_disjunction_to_list_of_literals F L,
	gs_member Theory Theories,
	gs_list_of_T_literals Hyp Theory L L1,
	not (L1 = nil),
	gs_member Literal L1,
	gs_convert_to_oyster_syntax Literal O,
	OysterString is (O ^ "."),
	externalcall "gs_solve_pia" OysterString Output,!,
	gs_delete_from_list Literal L1 L2, !,
	Output1 is (Output ^ "."),
%printstdout Theories,
printstdout "Solved literal is: ",
printstdout Output1,
	gs_string_to_term Output1 SolvedLiteral,
printstdout "Term is: ",
printstdout SolvedLiteral,
	append L2 [ SolvedLiteral ] L3,
	gs_list_of_literals_to_disjunction L3 FF.


gs_entail_cooper Hyp gs_pia F FF :-
	gs_disjunction_to_list_of_literals F L,
	gs_list_of_T_literals Hyp gs_pia L L1,
	not (L1 = nil),
	gs_diff L L1 L2, 
	gs_member (otype_of Var nat) Hyp,
	gs_number_of_occs_in_list Var L1 N,
	N > 0,
	gs_number_of_occs_in_list Var L2 0,
	gs_convert_list_to_oyster_syntax L1 OysterStrings,
	gs_make_one_string_disj OysterStrings OString0,
	term_to_string Var VarS,
	S is (VarS ^ ":pnat=>"),
	OString1 is (S ^ OString0),
	externalcall "gs_cooper" OString1 Output,!,
	Output1 is (Output ^ "."),
	gs_string_to_term Output1 F1,
	append [ F1 ] L2 L3,
	gs_list_of_literals_to_disjunction L3 FF.


gs_entail_hodes Hyp gs_pia F FF :-
	gs_disjunction_to_list_of_literals F L,
	gs_list_of_T_literals Hyp gs_pia L L1,
	not (L1 = nil),
	gs_diff L L1 L2, 
	gs_member (otype_of Var nat) Hyp,
	gs_number_of_occs_in_list Var L1 N,
	N > 0,
	gs_number_of_occs_in_list Var L2 0,
	gs_convert_list_to_oyster_syntax L1 OysterStrings,
	gs_make_one_string_disj OysterStrings OString0,
	term_to_string Var VarS,
	S is (VarS ^ ":pnat=>"),
	OString1 is (S ^ OString0),
	externalcall "gs_hodes" OString1 Output,!,
	Output1 is (Output ^ "."),
	gs_string_to_term Output1 F1,
	append [ F1 ] L2 L3,
	gs_list_of_literals_to_disjunction L3 FF.

gs_simplify_t Hyp gs_pia F FF :-
	gs_disjunction_to_list_of_literals F L,
	gs_list_of_T_literals Hyp gs_pia L L1,
	not (L1 = nil),
	gs_diff L L1 L2, 
	gs_convert_list_to_oyster_syntax L1 OysterStrings,
	gs_make_one_string_disj OysterStrings OString,
	externalcall "gs_simpl_pia" OString Output,
	Output1 is (Output ^ "."),
	gs_string_to_term Output1 F1,
	append [ F1 ] L2 L3,
	gs_list_of_literals_to_disjunction L3 FF.



%
% (1) kada nije trueP nece da radi (npr. gs_ccc)
% (2) kod backtrackinga nece da radi (npr. gs_entail_no)



gs_valid_t Hyp Theories F :-
	gs_disjunction_to_list_of_literals F L,
	gs_member Theory Theories,
%printstdout L,
%printstdout "---> > > ------>",
%printstdout Hyp,
%printstdout Theory,
	gs_list_of_T_literals Hyp Theory L L1,
	not (L1 = nil),
%printstdout L1,
	gs_valid Theory L1,!,
printstdout "------- Subset of clauses valid in -------->",
printstdout Theory.

gs_valid gs_pia L :-
	gs_convert_list_to_oyster_syntax L OysterStrings,
	gs_make_one_string_disj OysterStrings OString,
	externalcall "gs_valid_pia" OString Output,!,
	Output = "trueP".


gs_valid gs_objlists L :-
	gs_exhaustivelly_rewrite_list_with_rules [ ax1, ax2, ax3 ] L L1,
	gs_negate_all_literals L1 L2,
	gs_convert_list_to_oyster_syntax L2 OysterStrings,
	gs_make_one_string_conj OysterStrings OString,
	externalcall "gs_ccc" OString Output, !,
	Output = "trueP".

gs_valid gs_pure_equality L :-
%printstdout L,
	gs_negate_all_literals L L2,
	gs_convert_list_to_oyster_syntax L2 OysterStrings,
%printstdout  OysterStrings,
	gs_make_one_string_conj OysterStrings OString,
%printstdout OString,
	externalcall "gs_ccc" OString Output, !,
	Output = "trueP".

gs_ccc F FF :-
	gs_disjunction_to_list_of_literals F L,
	gs_negate_all_literals L L1,
	gs_convert_list_to_oyster_syntax L1 OysterStrings,
	gs_make_one_string_conj OysterStrings OString,
	externalcall "gs_ccc" OString LString, !,
	LString1 is (LString ^ "."),
	printstdout LString1,
	gs_string_to_term LString1 FF, !,
	pprint_string "String-to-term finished, term is: ",
	pprint_name FF.



% ***************************************************************
% Sockets 
%
% Authors: Gordon Reid and Predrag Janicic
%

% To become a client of a Quintus tcp server we need
% to lookup the hostname and port from a file,
% then initialise the connection, then loop.

gs_string_to_term S T :-
%	printstdout ">>>>>",
%	printstdout S,
	string_to_term S T.
%	printstdout "<<<<<".

externalcall Pred InputString OutputString :-
	printstdout "< External procedure called.",
	printstdout Pred, 
	open_in "/tmp/serverfile" In,
	input_line In Input,
	X is substring Input 0 10,
   	Newstring is X ^ ".",
%	printstdout Newstring,
	gs_string_to_term Newstring (port Port),
	open_socket "localhost" Port InStream OutStream,
	GoalString is (((Pred ^ "('") ^ InputString ) ^ "')"),
	printstdout GoalString,
	S is (("term(" ^ GoalString) ^ ").\n"),
	output OutStream S,
 	flush OutStream,
	printstdout "String sent",
	input_line InStream OutputConnectedString,
	input_line InStream OutputString0,
	printstdout "> Response recieved",
	SizeU0 is size OutputString0,
	SizeU is SizeU0 - 1,
	OutputString is substring OutputString0 0 SizeU,
	printstdout OutputString,
	S1 is size OutputString,
	printstdout "Size = ",
	printstdout S1,
	!.




end

