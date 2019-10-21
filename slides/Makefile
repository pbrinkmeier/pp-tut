NAME = 01_Haskell_Basics

.PHONY: clean

$(NAME).pdf: $(NAME).tex code/* demos/*
	mkdir -p build
	latexmk -pdf -jobname=build/$(NAME) $(NAME).tex
	cp build/$(NAME).pdf $(NAME).pdf

clean:
	rm -rf build
