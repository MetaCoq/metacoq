all: coq

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: install html clean mrproper all

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

.merlin: Makefile.coq
	$(MAKE) -f $< $@

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
