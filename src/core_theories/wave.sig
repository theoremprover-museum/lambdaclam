/*

File:  wave.sig
Author: Louise Dennis / James Brotherston
Description: Support for Rippling
Last Modified: 20th August 2002

*/

sig wave.

accum_sig rewriting.


kind ripFail type.

type failed_sink etree -> osyn -> ripFail.
type failed_embed rewrite_rule -> ripFail.
type failed_cond rewrite_rule -> ripFail.

%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Wave Methods
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%

type wave theory.

type wave_method dir -> rewrite_rule ->  meth.
type wave_method_inst rewrite_rule ->  meth.
type wave_case_split rewrite_rule -> meth.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Critics
%% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* type case_split crit. */
type wave_critic_strat crit.
type wave_patch ripFail -> (list int) -> rewrite_rule -> crit.
type wave_failure ripFail -> rewrite_rule -> crit.
type check_wave_case_split rewrite_rule -> crit.

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Support Predicates
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%

type ripple_rewrite (list osyn) -> rewrite_rule -> (pairing osyn (list etree)) -> (pairing osyn (list etree)) -> osyn -> (list int) -> dir -> (list context) -> int -> o.

type congr_ripple_skel (list etree) -> (list int) -> int -> (list etree) -> (list (list etree)) -> osyn -> o.

type reform_emb int -> (list etree) -> (list etree) -> (list (list etree)) -> (list etree) -> osyn -> o.
type remove_positions etree -> etree -> o.


type sinkable etree -> (list int) -> o.

type embeds_list (list etree) -> osyn -> (list etree) -> (list etree) -> (list etree) -> o.
type   measure_check dir -> (list etree) -> (list etree)  -> (list int) -> (list etree) -> int -> o.

type strip_forall_embeds osyn -> etree -> osyn -> o.

type induction_hypothesis (list osyn) -> (list osyn) -> (list osyn) -> o.
type ind_hyp hyp_ann.
type wrule hyp_ann.

type modify_embedding etree -> etree -> o.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  METHODS
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type   set_up_ripple     meth.        % meta-level step (find embedding)
type   post_ripple       meth.   % meta-level step (throw away embedding)


end
