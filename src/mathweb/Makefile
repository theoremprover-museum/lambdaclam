LCLAM_SRC=$(LCLAM_HOME)/src
UTIL_DIR=$(LCLAM_SRC)/util
LCLAM=$(LCLAM_SRC)/planner
THEORY_DIR=$(LCLAM_SRC)/theories
TRACEDIR=$(LCLAM_SRC)/io

all:  clean mw_top.lp
clean:
	command rm *.lp

%.lp: %.mod
	tjcc -p $(UTIL_DIR) -p $(THEORY_DIR) -p $(TRACEDIR) $<
%.mod: %.sig
