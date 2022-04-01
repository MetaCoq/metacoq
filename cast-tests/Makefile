all: examples

examples: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=$(TIMED)

Makefile.coq: Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq