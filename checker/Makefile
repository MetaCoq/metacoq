all: plugin coq

coq: plugin Makefile.coq
	$(MAKE) -f Makefile.coq

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

plugin:
	$(MAKE) -C gen-src
	sh update_plugin.sh

install:
	$(MAKE) -f Makefile.coq install

.PHONY: plugin

clean:
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq _CoqProject
