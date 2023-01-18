all: theory

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.erasure: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.erasure $(DEPS)

theory: Makefile.erasure
	$(MAKE) -f Makefile.erasure

install: theory
	$(MAKE) -f Makefile.erasure install

uninstall: Makefile.erasure
	$(MAKE) -f Makefile.erasure uninstall

clean: Makefile.erasure
	make -f Makefile.erasure clean

mrproper:
	rm -f Makefile.erasure

.merlin:
	make -f $< $@

vos: Makefile.erasure
	$(MAKE) -f Makefile.erasure vos

quick: Makefile.erasure
	$(MAKE) -f Makefile.erasure COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
