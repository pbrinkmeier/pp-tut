NAME = 01_Haskell_Basics

.PHONY: clean

%.pdf: %.tex code/* demos/* images/*
	mkdir -p build
	latexmk -pdf -jobname=build/$(basename $@) $<
	cp build/$@ $@

clean:
	rm -rf build *.pdf
