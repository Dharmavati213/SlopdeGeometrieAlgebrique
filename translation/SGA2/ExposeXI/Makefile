TEX := SGA2-XI.tex

.PHONY: all pdf clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(TEX)

clean:
	latexmk -C $(TEX)
