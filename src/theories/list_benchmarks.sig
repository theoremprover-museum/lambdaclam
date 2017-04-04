/*

File: list_benchmarks.sig
Author: Louise Dennis
Description:  List based theorems for benchmarking.
Last Modified: 20th March 2001

*/

sig list_benchmarks.

accum_sig objlists.
accum_sig constructive_logic.

type list_benchmarks theory.

type qrev osyn.
type rotate osyn.
type drop osyn.
type atend osyn.
type omember osyn.

type qrev1 rewrite_rule.
type qrev2 rewrite_rule.
type rotate1 rewrite_rule.
type rotate2 rewrite_rule.
type drop1 rewrite_rule.
type drop2 rewrite_rule.
type drop3 rewrite_rule.
type omem1 rewrite_rule.
type omem2 rewrite_rule.
type omem3 rewrite_rule.
type atend1 rewrite_rule.
type atend2 rewrite_rule.

type qrevcorrect query.
type rotlensimple query.
type app1right query.
type apporev query.
type cnc_app query.
type cnc_cons query.
type cnc_cons2 query.
type comapp query.
type lenorev query.
type lensum query.
type leqnth query.
type memapp2 query.
type memapp3 query.
type memorev query.
type nthapp query.
type nthmem query.
type nthnil query.
type orevqrev query.
type qrevqrev query.
type orevorev query.
type rotlen query.
type singleorev query.
type tailorev query.
type tailorev2 query.
type lendouble query.
type appatend query.
type allList_omember query.
type allList_omember_imp1 query.
type allList_omember_imp2 query.
type simple_sy query.
type memapp query.

% from myp_benchmarks

type map_benchmarks theory.

type mapcar osyn.
type fil osyn.
type foldr osyn.

type mapcar1 rewrite_rule.
type mapcar2 rewrite_rule.
type fil1 rewrite_rule.
type fil2 rewrite_rule.
type fil3 rewrite_rule.
type foldr1 rewrite_rule.
type foldr2 rewrite_rule.

type filapp query.
type mapcarapp query.
type mapdouble query.
type mapfoldr query.
type mapthm query.
type lenmap query.
type mapapn query.
end

