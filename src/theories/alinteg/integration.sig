/*

File: real_integ.mod
Author: Alex Heneveld
Description: tying them all together...
Created: Nov 02 (based on work in Jan 00)

*/

sig integration.

accum_sig real_integ.

type integration theory.

type do_all_tests o.

type evaluate osyn -> osyn -> osyn -> o.
type evaluation_query osyn -> osyn -> query.
type alinteg_evaluate_top_meth osyn -> meth.

type help o.
type sample int -> o.
type sample int -> o.
type sample int -> o.
type help_real_queries o.

type alinteg_module theory -> o.
