/*

File: pwf.mod
Author: Louise Dennis
Description: Piecewise Fertilisation as described in BBNote 1286
Created:  October 7th 2002

*/

module pwf.

accumulate unblocking.

local memb_under_forall osyn -> (list osyn) -> o.

atomic pwf imp_ifert
        (seqGoal (Hyps >>> (app imp [Ap, Bp])) Context)
        (not (Ap = Bp),
	induction_hypothesis Hyps H _,
	 memb_under_forall (app imp [A, B]) H ,
	 % should be that A and Ap have the same skeleton but
	 % we have no theory for annotations in the hypotheses
	 embeds EA A Ap,
	 embeds EB B Bp)
        (filter Context NewContext (H1\ (sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	update_gb_context (seqGoal (((hyp Ap ind_hyp)::Hyps) >>> A) ((embedding_context [EA] inout)::NewContext) ** (seqGoal (((hyp B ind_hyp)::Hyps) >>> Bp) ((embedding_context [EB] inout)::NewContext))) NewGoals [])
	NewGoals
	notacticyet.

atomic pwf or_fert
	(seqGoal (Hyps >>> G) Context)
	(induction_hypothesis Hyps H Rest,
%%	 memb_under_forall (app exists [T, (abs (X\ (app or [(A X), (B X)])) T)]) H,
%%	findall (E\ (strip_forall_embeds (app exists [T, (abs (X\ (A X)) T)]) E G)) EA,
%%	findall (E\ (strip_forall_embeds (app exists [T, (abs (X\ (B X)) T)]) E G)) EB)
	 memb_under_forall (app or [A, B]) H,
	findall (E\ (embeds E A G)) EA,
	findall (E\ (embeds E B G)) EB)
	(copy_term [G] [G1],
	filter Context NewContext (H1\
		(sigma A\ (sigma B\ (H1 = (embedding_context A B))))),
	update_gb_context (seqGoal (((hyp A ind_hyp)::Rest) >>> G) ((embedding_context EA inout)::NewContext) ** (seqGoal (((hyp B ind_hyp)::Rest) >>> G1) ((embedding_context EB inout)::NewContext))) NewGoals [])
	NewGoals
	notacticyet.

compound pwf piecewise_fertilisation
         (repeat_meth
		(orelse_meth imp_ifert or_fert))
        _
        true.

memb_under_forall Term ((hyp Term _)::_).
memb_under_forall Term ((hyp (app forall [Ty, (abs P Ty)]) _)::T):-
        memb_under_forall Term ((hyp (P A) _)::T).
memb_under_forall Term (_H::T):-
        memb_under_forall Term T.
		  
     

end
