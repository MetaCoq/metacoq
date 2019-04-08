TOCOPY=tm_util quoted quoter constr_quoter template_monad denoter denote plugin_core
all: coq plugin

gen-src/Extraction.vo: coq gen-src/Extraction.v
	$(COQPATH)coqc -I src -Q theories Template gen-src/Extraction.v

plugin: coq Makefile.plugin gen-src/Extraction.vo
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

Makefile.plugin: coq _PluginProject  $(TOCOPY:%=gen-src/%.ml)
	$(COQPATH)coq_makefile -f _PluginProject -o Makefile.plugin

.merlin: Makefile.coq
	$(MAKE) -f Makefile.coq .merlin

gen-src/%.ml: src/%.ml
	ln -s ../$< $@

clean-plugin:
	(cd gen-src; rm -rf *.d *.c* $(TOCOPY:%=%.ml) )
