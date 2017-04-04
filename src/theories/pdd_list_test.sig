/*

File: objlists.sig
Author: Louise Dennis
Description: A Theory for Lists
Last Modified: 20th March 2001

*/

sig pdd_list_test.

accum_sig pdd_test_arith.

type o1app osyn.
type o2app osyn.
type o3app osyn.
type o4app osyn.
type omember osyn.
type removeAll osyn.
type removeOne osyn.

type o1app2 rewrite_rule.
type o2app1 rewrite_rule.
type o2app2 rewrite_rule.
type o3app1 rewrite_rule.
type o3app2 rewrite_rule.
type o4app1 rewrite_rule.
type o4app2 rewrite_rule.
type removeAll1 rewrite_rule.
type removeAll2 rewrite_rule.
type removeAll3 rewrite_rule.
type removeOne1 rewrite_rule.
type removeOne2 rewrite_rule.
type removeOne3 rewrite_rule.
type omem1 rewrite_rule.
type omem2 rewrite_rule.
type omem3 rewrite_rule.

type assapp1 query.
type assapp2 query.
type assapp3 query.
type assapp4 query.
type removeAllthm query.

type	pdd_list_test theory.

type    olist   osyn -> osyn.

type    onil         osyn.
type    ocons        osyn.
type    oapp         osyn.
type    olength      osyn.
type    orev         osyn.
type    allList 	osyn.

type    oapp1           rewrite_rule.
type    oapp2           rewrite_rule.
type    ass_oapp        rewrite_rule.
type    cons_functional rewrite_rule.
% type    neq_cons_nil    rewrite_rule.
% type    neq_nil_cons    rewrite_rule.
type    m1	        rewrite_rule.
type    olength1        rewrite_rule.
type    olength2        rewrite_rule.
type    orev1           rewrite_rule.
type    orev2           rewrite_rule.
type    allList1        rewrite_rule.
type    allList2        rewrite_rule.
type    allList_or_l    rewrite_rule.
type    allList_or_r    rewrite_rule.

type assapp         query.
type all_list       query.
type all_list_cv    query.
type all_list_sy    query.
type allList_and_dist query.
type allList_and_dist_cv query.
type allList_or_left  query.
type allList_or_right query.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%%  INDUCTION SCHEMES FOR LISTS
%%

type list_struct       scheme.
type list_twostep      scheme.

end

