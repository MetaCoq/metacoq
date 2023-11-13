all: theory

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.safechecker: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.safechecker $(DEPS)

theory: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker

install: theory
	$(MAKE) -f Makefile.safechecker install

uninstall: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker uninstall

clean: Makefile.safechecker
	make -f Makefile.safechecker clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.safechecker _CoqProject

.merlin: Makefile.safechecker
	make -f $< $@

vos: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker vos

quick: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
