LCLAM_DOC=$(LCLAM_HOME)/doc

manual:
	latex manual
	bibtex manual
	makeindex manual
	latex manual
	latex manual
	dvips manual -o manual.ps

clean:
	rm *.dvi
	rm *.aux
	rm *.log
	rm *.toc
	rm *.bbl
	rm *.blg
	rm *.idx
	rm *.ind
	rm manual.ps
	rm release_notes/*.dvi
	rm release_notes/*.aux
	rm release_notes/*.ps
