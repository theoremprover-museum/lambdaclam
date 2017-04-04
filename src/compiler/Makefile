
envparser: envgrammar
	tjsim -s "genparser \"sbrc\" \"envgrammar\" \"envparser\"." -b envgrammar
	tjcc -p $(LCLAM_HOME)/src/planner/ -p $(LCLAM_HOME)/src/util/ -p $(LCLAM_HOME)/src/theories/ -p $(LCLAM_HOME)/src/io/ envparser


envgrammar: envgrammar.sig envgrammar.mod
	tjcc -p $(LCLAM_HOME)/src/planner/ -p $(LCLAM_HOME)/src/util/ -p $(LCLAM_HOME)/src/theories/ -p $(LCLAM_HOME)/src/io/ envgrammar

postprocess: postprocess.sig postprocess.mod
	tjcc -p $(LCLAM_HOME)/src/planner/ -p $(LCLAM_HOME)/src/util/ -p $(LCLAM_HOME)/src/theories/ -p $(LCLAM_HOME)/src/io/ postprocess

