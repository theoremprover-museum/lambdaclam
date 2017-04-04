all:
	make frame.lp
	make ftl.lp

clean:
	rm -f *.lp

%.lp: %.mod
	tjcc $<

%.mod: %.sig
