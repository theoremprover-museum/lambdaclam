LCLAM_SRC=$(LCLAM_HOME)/src
UTIL_DIR=$(LCLAM_SRC)/util
LCLAM=$(LCLAM_SRC)/planner
THEORY_DIR=$(LCLAM_SRC)/theories
TRACEDIR=$(LCLAM_SRC)/io
CORE_THEORIES=$(LCLAM_SRC)/core_theories
INTERFACE=$(LCLAM_SRC)/interface

ripple_book.mod: clam_corpus.mod

pdd_list_test.mod: pdd_test_arith.mod

pdd_test_arith.mod: pdd_repair.mod

clam_corpus.mod: list_benchmarks.mod

list_benchmarks.mod: objlists.mod constructive_logic.mod

ordinal.mod: arithmetic.mod constructive_logic.mod

synthesis_ex.mod: list_benchmarks.mod

lim_plus.mod: arithmetic.mod constructive_logic.mod

objlists.mod: arithmetic.mod

arithmetic.mod: ../interface/lclam.mod

whisky.mod: arithmetic.mod constructive_logic.mod

map_benchmarks.mod: list_benchmarks.mod

challenges.mod: list_benchmarks.mod

clam_corpus2.mod: list_benchmarks.mod

clam_corpus3.mod: list_benchmarks.mod

smaill_green_syn_ex.mod: clam_corpus.mod

yoshidaetal.mod: clam_corpus.mod

ireland_critics.mod: clam_corpus.mod

ireland_critics_lemma_spec.mod: clam_corpus.mod

control_divides.mod: arithmetic.mod

pdd_repair.mod: map_benchmarks.mod constructive_logic.mod

# in core_theories

../core_theories/wave_critics.mod: ../core_theories/induction.mod

../core_theories/induction.mod: ../core_theories/schemes.mod ../core_theories/generalise.mod ../core_theories/pwf.mod 

../core_theories/pwf.mod: ../core_theories/unblocking.mod

../core_theories/unblocking.mod: ../core_theories/wave.mod

../core_theories/wave.mod: ../core_theories/casesplit.mod

../core_theories/casesplit.mod: ../core_theories/rewriting.mod

../core_theories/rewriting.mod: ../core_theories/embed.mod

../core_theories/embed.mod: ../core_theories/logic_eq_constants.mod

../core_theories/generalise.mod: ../core_theories/coerce_meta_vars.mod

../core_theories/coerce_meta_vars.mod: ../core_theories/conjecture_tester.mod

../core_theories/conjecture_tester.mod: ../core_theories/test_set_gen.mod

# in interface

../interface/lclam.mod: ../interface/theory_db.mod ../planner/planner.mod

../interface/theory_db.mod: ../core_theories/wave_critics.mod

# in planner

../planner/planner.mod: ../planner/pds_planner.mod ../planner/part_plan.mod ../planner/pds_support.mod ../io/pretty_printer.mod ../syntax/lclam_syntax.mod ../io/sockets.mod

../planner/pds_support.mod: ../planner/plan_support.mod

../planner/pds_support.sig: ../io/pretty_printer.sig ../planner/switch.sig

../planner/plan_support.mod: ../planner/switch.mod

# in syntax

../syntax/syntax.sig: ../syntax/basic_types.sig ../util/lclam_utils.sig

../syntax/lclam_syntax.mod: ../syntax/goal.mod ../syntax/syntax.mod ../syntax/critics.mod ../util/lclam_utils.mod

../syntax/critics.mod: ../syntax/method.mod

# in util

../util/lclam_utils.mod: ../util/lclam_list.mod ../util/lclam_map.mod


%.mod: %.sig
	touch $@

%.sig:
	touch $@

%.lp: %.mod 
	$(TEYJUS_HOME)/tjcc -p $(LCLAM) -p $(TRACEDIR) -p $(UTIL_DIR) -p $(CORE_THEORIES) -p $(INTERFACE) $<

clean:
	command \rm *.lp

