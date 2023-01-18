all: theory

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.templatepcuic: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.templatepcuic $(DEPS)

theory: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic

install: theory
	$(MAKE) -f Makefile.templatepcuic install

uninstall: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic uninstall

clean: Makefile.templatepcuic
	make -f Makefile.templatepcuic clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.templatepcuic _CoqProject

.merlin:
	make -f $< $@

vos: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic vos

quick: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
