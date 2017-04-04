LCLAM_SRC=$(LCLAM_HOME)/src
UTIL_DIR=$(LCLAM_SRC)/util
LCLAM=$(LCLAM_SRC)/planner
THEORY_DIR=$(LCLAM_SRC)/theories
TRACEDIR=$(LCLAM_SRC)/io
FTLDIR=./ftl

all:
	make bridge.lp

clean:
	rm -f *.lp

%.lp: %.mod
	tjcc -p $(LCLAM) -p $(TRACEDIR) -p $(UTIL_DIR) -p $(THEORY_DIR) -p $(FTLDIR) $<

%.mod:
	%.sig

bridge.mod:
	fi.mod

fi.mod:
	foltl.mod
