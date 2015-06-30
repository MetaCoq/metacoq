coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
