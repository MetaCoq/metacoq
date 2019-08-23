all: theory

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.pcuic: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.pcuic $(DEPS)

theory: Makefile.pcuic
	$(MAKE) -f Makefile.pcuic

install: theory plugin
	$(MAKE) -f Makefile.pcuic install

clean: Makefile.pcuic Makefile.plugin
	make -f Makefile.pcuic clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.pcuic _CoqProject

.merlin:
	make -f Makefile.plugin .merlin
