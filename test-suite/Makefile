.PHONY: all bugd clean mrproper plugin-demo

all: bugs plugin-demo

bugs: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=$(TIMED)

Makefile.coq: Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

plugin-demo:
	$(MAKE) -C plugin-demo

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
