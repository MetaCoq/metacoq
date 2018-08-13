all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
