/*

File: embed.sig
Author: Louise Dennis / James Brotherston
Description:  Embeddings (as used by rippling)
Last Modified: 20th August 2002

*/

sig embed.

accum_sig logic_eq_constants, pairs.


% tree is embedding of second argument into third argument.

type embeds        etree -> osyn -> osyn -> o.

type set_epos etree -> osyn -> o.

% An ordering on embeddings.

type check_measure_reducing dir -> etree -> etree -> (list int) -> etree -> int -> o.

type nwf dir.
type nwfb dir.
type uiwf dir.
type uowf dir.
type lo dir.
type li dir.
type new dir.
type pnew dir.

kind branch_var_status type.

type so branch_var_status.
type ind_var branch_var_status.
type ind_var_nowf branch_var_status.

kind embedding_status type.
type nu embedding_status.
%% no unaccounted for wave fronts
type nwfo embedding_status.
%% no missing or new wave front.
type si embedding_status.
%% surplus inward wave front.
type do embedding_status.
%% deficit outward wave front.

end















