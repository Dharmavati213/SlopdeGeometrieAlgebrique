TEX := SGA1-Expose-VI-fibered-categories-EN.tex

.PHONY: all pdf clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX)

clean:
	latexmk -C
