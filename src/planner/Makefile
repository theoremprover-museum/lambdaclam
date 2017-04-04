LCLAM_SRC=$(LCLAM_HOME)/src
UTIL_DIR=$(LCLAM_SRC)/util
LCLAM=$(LCLAM_SRC)/planner
THEORY_DIR=$(LCLAM_SRC)/theories
TRACEDIR=$(LCLAM_SRC)/io

all: test.lp

clean:
	rm test.lp

%.lp: %.mod
	$(TEYJUS_HOME)/tjcc -p $(UTIL_DIR) -p $(THEORY_DIR) -p $(TRACEDIR) $<

test.mod: ../theories/objlists.mod ../theories/constructive_logic.mod

%.mod: %.sig
	touch $@

%.sig:
	touch $@
