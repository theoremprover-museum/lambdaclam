LCLAM_SRC=$(LCLAM_HOME)/src
UTIL_DIR=$(LCLAM_SRC)/util
LCLAM=$(LCLAM_SRC)/planner
THEORY_DIR=$(LCLAM_SRC)/theories
TRACEDIR=$(LCLAM_SRC)/io

clean:
	command rm *.lp

ex3.mod: ../objlists.mod ../constructive_logic.mod

ex2.mod: ../objlists.mod ../constructive_logic.mod

%.lp: %.mod
	$(TEYJUS_HOME)/tjcc -p $(LCLAM) -p $(TRACEDIR) -p $(UTIL_DIR) -p $(THEORY_DIR) $<

%.mod: %.sig
	touch $@

%.sig:
	touch $@


