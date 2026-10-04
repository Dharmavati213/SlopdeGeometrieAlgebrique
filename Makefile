.PHONY: all lean tex clean

all: lean tex

lean:
	cd lean && lake build

SGA1_TEX_DIRS := \
	translation/SGA1/Introduction \
	translation/SGA1/ExposeI \
	translation/SGA1/ExposeII \
	translation/SGA1/ExposeIII \
	translation/SGA1/ExposeIV \
	translation/SGA1/ExposeV \
	translation/SGA1/ExposeVI \
	translation/SGA1/ExposeVIII \
	translation/SGA1/ExposeIX \
	translation/SGA1/ExposeX \
	translation/SGA1/ExposeXI \
	translation/SGA1/ExposeXII \
	translation/SGA1/ExposeXIII

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
	@for d in $(SGA1_TEX_DIRS) $(SGA2_TEX_DIRS); do $(MAKE) -C $$d || exit 1; done
	$(MAKE) -C translation/SGA3 book

clean:
	cd lean && lake clean
	@for d in $(SGA1_TEX_DIRS) $(SGA2_TEX_DIRS); do $(MAKE) -C $$d clean; done
	$(MAKE) -C translation/SGA3 clean
