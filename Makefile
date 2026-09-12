.PHONY: all lean tex clean

all: lean tex

lean:
	cd lean && lake build

tex:
	$(MAKE) -C translation/SGA1/ExposeI
	$(MAKE) -C translation/SGA1/ExposeVI

clean:
	cd lean && lake clean
	$(MAKE) -C translation/SGA1/ExposeI clean
	$(MAKE) -C translation/SGA1/ExposeVI clean
