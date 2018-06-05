all: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: all install html clean mrproper

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper: clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.merlin: Makefile.coq
	$(MAKE) -f Makefile.coq .merlin
