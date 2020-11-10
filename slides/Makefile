.PHONY: clean

%.pdf: %.tex code/*
	mkdir -p build
	latexmk -shell-escape -pdf -jobname=build/$(basename $@) $<
	cp build/$@ $@

clean:
	rm -rf build *.pdf
