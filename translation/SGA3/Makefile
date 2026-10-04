PDFS := Introduction/SGA3-Intro.pdf \
 ExposeI/SGA3-I.pdf ExposeII/SGA3-II.pdf ExposeIII/SGA3-III.pdf \
 ExposeIV/SGA3-IV.pdf ExposeV/SGA3-V.pdf \
 ExposeVIA/SGA3-VIA.pdf ExposeVIB/SGA3-VIB.pdf \
 ExposeVIIA/SGA3-VIIA.pdf ExposeVIIB/SGA3-VIIB.pdf \
 ExposeVIII/SGA3-VIII.pdf ExposeIX/SGA3-IX.pdf ExposeX/SGA3-X.pdf \
 ExposeXI/SGA3-XI.pdf ExposeXII/SGA3-XII.pdf ExposeXIII/SGA3-XIII.pdf \
 ExposeXIV/SGA3-XIV.pdf ExposeXV/SGA3-XV.pdf ExposeXVI/SGA3-XVI.pdf \
 ExposeXVII/SGA3-XVII.pdf ExposeXVIII/SGA3-XVIII.pdf \
 ExposeXIX/SGA3-XIX.pdf ExposeXX/SGA3-XX.pdf ExposeXXI/SGA3-XXI.pdf \
 ExposeXXII/SGA3-XXII.pdf ExposeXXIII/SGA3-XXIII.pdf \
 ExposeXXIV/SGA3-XXIV.pdf ExposeXXV/SGA3-XXV.pdf ExposeXXVI/SGA3-XXVI.pdf
DIRS := $(patsubst %/,%,$(dir $(PDFS)))

.PHONY: all check pdf book clean $(DIRS)
all: check
	$(MAKE) pdf
	python3 check_coverage.py --require-pdf

check:
	python3 check_coverage.py

pdf: $(DIRS)

$(DIRS):
	$(MAKE) -C $@

book: all
	latexmk -pdf -interaction=nonstopmode -halt-on-error SGA3-English.tex

clean:
	@for d in $(DIRS); do $(MAKE) -C $$d clean || exit 1; done
	latexmk -C SGA3-English.tex
