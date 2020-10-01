all: Makefile.coq
	$(MAKE) -f Makefile.coq pretty-timed

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject 
	cat _CoqProject.in >> _CoqProject

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

install: all
	$(MAKE) -f Makefile.coq install

uninstall: all
	$(MAKE) -f Makefile.coq uninstall

mrproper:
	rm -f Makefile.coq
