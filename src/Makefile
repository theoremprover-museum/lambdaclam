LCLAM_SRC=$(LCLAM_HOME)/src
UTIL_DIR=$(LCLAM_SRC)/util
LCLAM=$(LCLAM_SRC)/planner
THEORY_DIR=$(LCLAM_SRC)/theories
TRACEDIR=$(LCLAM_SRC)/io

all:	
	cd $(LCLAM); make test.lp

clean:	
	cd $(LCLAM); make clean

allclean:
	cd $(THEORY_DIR)/tutorial; make clean
	cd $(THEORY_DIR); make clean
	cd $(LCLAM); make clean

benchmarks:
	cd $(LCLAM); make test.lp
	cd $(THEORY_DIR); make ordinal.lp
	cd $(THEORY_DIR); make whisky.lp
	cd $(THEORY_DIR)/tutorial; make ex3.lp
	cd $(THEORY_DIR)/tutorial; make ex2.lp
	cd $(THEORY_DIR); make map_benchmarks.lp
	cd $(THEORY_DIR); make list_benchmarks.lp
	cd $(THEORY_DIR); make challenges.lp
	cd $(THEORY_DIR); make clam_corpus.lp
	cd $(THEORY_DIR); make clam_corpus2.lp
	cd $(THEORY_DIR); make clam_corpus3.lp
	cd $(THEORY_DIR); make ireland_critics.lp
	cd $(THEORY_DIR); make ireland_critics_lemma_spec.lp
	cd $(THEORY_DIR); make lim_plus.lp
	cd $(THEORY_DIR); make smaill_green_syn_ex.lp
	cd $(THEORY_DIR); make yoshidaetal.lp
	cd $(THEORY_DIR); make control_divides.lp
	cd $(THEORY_DIR); make pdd_list_test.lp
	cd $(THEORY_DIR); make ripple_book.lp

