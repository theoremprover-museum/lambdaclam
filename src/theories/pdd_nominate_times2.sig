/*

File: arithmetic.sig
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2001

*/

sig pdd_nominate_times2.

accum_sig pdd_nominate.
accum_sig constructive_logic.

type pdd_nominate_times2 theory.


/* SYNTAX CONSTANTS */

type 	undef 	osyn. % maybe this should go somewhere else 
		    	% e.g. a partial functions theory.

% type    nat     osyn.
type	integer osyn.

type    zero         osyn.
type    s            osyn.
type    plus         osyn.
type    otimes        osyn.
type    exp          osyn.

type    plus1           rewrite_rule.
type    plus2           rewrite_rule.
type    pdd_times1          rewrite_rule.
type    pdd_times2          rewrite_rule.
type    exp1            rewrite_rule.
type    exp2            rewrite_rule.
type    s_functional    rewrite_rule.
type    neq_s_zero      rewrite_rule.
type    neq_zero_s      rewrite_rule.
type    neq_eq          rewrite_rule.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  INDUCTION SCHEMES FOR NAT
%%

type nat_struct         scheme.
type twostep        scheme.
/* type nat_minus          scheme.
type s_to_ss_ind        scheme.
*/

/*  GOALS  */

type eqzero	    query.
type simple         query.
type simple_taut    query.
type assp           query.
type comm2           query.
type comp           query.
type falsearith	    query.
type plus2right	    query.
type dist           query.
type distr          query.
type assm           query.
type assp_sy        query.
type expplus        query.
type exptimes       query.
type pdd_leqrefl        query.
type pdd_leqsuc         query.
type pdd_leqsum	    query.
type doublehalf	    query.
type halfplus       query.
type plus1lem	    query.
type plusxx         query.
type zeroplus       query.
type zerotimes       query.
type doubleplus     query.
type halfdouble     query.
type doubletimes    query.
type doubletimes2    query.
type times2right    query.

end
