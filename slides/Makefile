NAME = 01_Haskell_Basics

.PHONY: clean

%.pdf: %.tex code/* demos/*
	mkdir -p build
	latexmk -pdf -jobname=build/$(basename $@) $<
	cp build/$@ $@

clean:
	rm -rf build
