/*

File: lxtest.mod
Author: Alex Heneveld
Description: predicates to aid with testing
Created: Nov 02

*/

sig lxtest.

accum_sig lclam.
accum_sig constructive_logic.

type lxtest theory.

type test_set		osyn -> (list A) -> o.
type do_test_battery	string -> (list o) -> (list o) -> 
			(o -> o) -> meth -> (list query) -> (list query) -> o.

type print_summary	string -> (list o) -> (list o) -> (list query) -> (list query) -> o.
type print_list_count	(list A) -> string -> o.

type print_results	string -> (list o) -> (list o) -> (list query) -> (list query) -> o.
type print_titled_list	       string -> (list A) -> o.
type print_prefixed_list       string -> (list A) -> o.

type print_item		A -> o.

type print_line_1	A -> o.
type print_line_2	A -> B -> o.
type print_line_3	A -> B -> C -> o.
type print_line_4	A -> B -> C -> D -> o.
type print_line_5	A -> B -> C -> D -> E -> o.

type run_tests		string -> (list o) -> (list o) -> o.
type run_anti_tests	string -> (list o) -> (list o) -> o.
type run_queries	string -> meth -> (list query) -> (list query) -> o.
type run_anti_queries	string -> meth -> (list query) -> (list query) -> o.

type nop o.
type flop o.
type with_nop o -> o.

type test_lxtest   o.
