.PHONY: all lean tex clean

all: lean tex

lean:
	cd lean && lake build

SGA2_TEX_DIRS := \
	translation/SGA2/Introduction \
	translation/SGA2/ExposeI \
	translation/SGA2/ExposeII \
	translation/SGA2/ExposeIII \
	translation/SGA2/ExposeIV \
	translation/SGA2/ExposeV \
	translation/SGA2/ExposeVI \
	translation/SGA2/ExposeVII \
	translation/SGA2/ExposeVIII \
	translation/SGA2/ExposeIX \
	translation/SGA2/ExposeX \
	translation/SGA2/ExposeXI \
	translation/SGA2/ExposeXII \
	translation/SGA2/ExposeXIII \
	translation/SGA2/ExposeXIV

tex:
	$(MAKE) -C translation/SGA1/ExposeI
	$(MAKE) -C translation/SGA1/ExposeII
	$(MAKE) -C translation/SGA1/ExposeVI
	@for d in $(SGA2_TEX_DIRS); do $(MAKE) -C $$d; done

clean:
	cd lean && lake clean
	$(MAKE) -C translation/SGA1/ExposeI clean
	$(MAKE) -C translation/SGA1/ExposeII clean
	$(MAKE) -C translation/SGA1/ExposeVI clean
	@for d in $(SGA2_TEX_DIRS); do $(MAKE) -C $$d clean; done
