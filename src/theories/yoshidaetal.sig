/*

File: yoshidaetal.sig
Author: Louise Dennis
Description: Examples taken from Coloured rippling:  An extension of a theorem proving heuristic.  Tetsuya Yoshisa, Alan Bundy, Ian Green, Toby Walsh, David Basin, ECAI 94.
Created: 14th September 2005

*/

sig yoshidaetal.

accum_sig clam_corpus.

type yoshidaetal theory.

type otree osyn -> osyn.

type onode osyn.
type oleaf osyn.

type tree_struct scheme.

type maxht osyn.
type minht osyn.
type tipcount osyn.
type nodecount osyn.
type duptree osyn.
type swap osyn.
type flattentree osyn.
type maptree osyn.

type maxht1 rewrite_rule.
type maxht2 rewrite_rule.
type minht1 rewrite_rule.
type minht2 rewrite_rule.
type tipcount1 rewrite_rule.
type tipcount2 rewrite_rule.
type nodecount1 rewrite_rule.
type nodecount2 rewrite_rule.
type flattentree1 rewrite_rule.
type flattentree2 rewrite_rule.
type duptree1 rewrite_rule.
type duptree2 rewrite_rule.
type swap1 rewrite_rule.
type swap2 rewrite_rule.
type maptree1 rewrite_rule.
type maptree2 rewrite_rule.

type lenoapp rewrite_rule.
type plusand rewrite_rule.
type assplus rewrite_rule.
type complus rewrite_rule.
type greaterand rewrite_rule.
type greatermax rewrite_rule.
type maxmin1 rewrite_rule.
type maxmin2 rewrite_rule.

type maxhtgeqminht query.
type tipcountswap query.
type tipcountnodecount query.
type tipcountduptree query.
type maxhtduptree query.
type swapswap query.
type flattenswap query.
type flattenmap query.
type lengthflattentree query.
type swapmaptree query.

end
