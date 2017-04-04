/*

File: clam_corpus.sig
Author: Louise Dennis
Description:  Clam theorems for benchmarking.
Last Modified: 28th May 2001

*/

sig clam_corpus.

accum_sig list_benchmarks.

type clam_corpus theory.


type sort  osyn.
type insert osyn.
type count osyn.
type odd osyn.
type fac osyn.
type geq osyn.
type greater osyn.
type intersect osyn.
type union osyn.
type min osyn.
type max osyn.
type ordered osyn.
type subset osyn.


type sort1 rewrite_rule.
type sort2 rewrite_rule.
type insert1 rewrite_rule.
type insert2 rewrite_rule.
type insert3 rewrite_rule.
type count1 rewrite_rule.
type count2 rewrite_rule.
type count3 rewrite_rule.
type odd1 rewrite_rule.
type odd2 rewrite_rule.
type odd3 rewrite_rule.
type fac1 rewrite_rule.
type fac2 rewrite_rule.
type intersect1 rewrite_rule.
type intersect2 rewrite_rule.
type intersect3 rewrite_rule.
type intersect4 rewrite_rule.
type union1 rewrite_rule.
type union2 rewrite_rule.
type union3 rewrite_rule.
type union4 rewrite_rule.
type ordered1 rewrite_rule.
type ordered2 rewrite_rule.
type ordered3 rewrite_rule.
type ordered4 rewrite_rule.
type subset1 rewrite_rule.
type subset2 rewrite_rule.
type subset3 rewrite_rule.
type subset_transitive rewrite_rule.
type geq1 rewrite_rule.
type geq2 rewrite_rule.
type geq3 rewrite_rule.
type geq_transitive rewrite_rule.
type greater1 rewrite_rule.
type greater2 rewrite_rule.
type greater3 rewrite_rule.
type greater_transitive rewrite_rule.
type min1 rewrite_rule.
type min2 rewrite_rule.
type min3 rewrite_rule.
type max1 rewrite_rule.
type max2 rewrite_rule.
type max3 rewrite_rule.

type memins1 rewrite_rule.
type memins2 rewrite_rule.


type countsort query.
type evenodd1 query.
type evenodd2 query.
type geqdouble query.
type geqdoublehalf query.
type geqhalf query.
type geqnotlessp query.
type greatercancel query.
type greatercons query.
type greaterplus query.
type greaterplus2 query.
type greaterplus3 query.
type greaters query.
type greaters2 query.
type greaterss query.
type greatertimes query.
type grsqsuc query.
type lensort query.
type less_double_mono query.
type less_double_mono2 query.
type lesseq query.
type lessleq1 query.
type lessleq2 query.
type lesss query.
type memins query.
type meminsert1 query.
type meminsert2 query.
type memintersect query.
type memsort1 query.
type memsort2 query.
type memunion1 query.
type memunion2 query.
type minmax query.
type minmaxgeq query.

type notlesstrans query.
type notlesstrans2 query.
type ordered_cons query.
type plusgeq query.
type plusgeq2 query.
type plusless query.
type subsetcons query.
type subsetintersect query.
type subsetunion query.
type times_less query.

end
