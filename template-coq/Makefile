all: coq plugin

gen-src/Extraction.vo: coq gen-src/Extraction.v
	$(COQPATH)coqc -I src -Q theories Template gen-src/Extraction.v

plugin: coq Makefile.plugin
	$(MAKE) -f Makefile.plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: all install html clean mrproper

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq Makefile.plugin
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.plugin clean

mrproper: clean
	rm -f Makefile.coq Makefile.plugin

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: coq _PluginProject
	$(COQPATH)coq_makefile -f _PluginProject -o Makefile.plugin

.merlin: Makefile.coq
	$(MAKE) -f Makefile.coq .merlin
