all: coq

coq: Makefile.coq Makefile.plugin
	$(MAKE) -f Makefile.coq
	$(MAKE) -f Makefile.plugin

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

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin

.merlin: Makefile.coq
	$(MAKE) -f Makefile.coq .merlin
