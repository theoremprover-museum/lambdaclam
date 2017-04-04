/*

File: real_trig.sig
Author: Alex Heneveld
Description: trig fns for reals
Created: Nov 02 (based on work in Jan 00)

*/

sig real_trig.

accum_sig real_fns.
	  
type real_trig theory.

type r_pi osyn.

type sin osyn.
type cos osyn.

type sin_zero rewrite_rule.
type cos_zero rewrite_rule.
type sin_pi rewrite_rule.
type cos_pi rewrite_rule.
type sin_pi_over_two rewrite_rule.
type cos_pi_over_two rewrite_rule.
type sin_neg_1 rewrite_rule.
type sin_neg_2 rewrite_rule.
type cos_neg_1 rewrite_rule.
type cos_neg_2 rewrite_rule.

type sin_plus rewrite_rule.
type cos_plus rewrite_rule.

