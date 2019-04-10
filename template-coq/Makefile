all: coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	cp src/template_coq.cmx src/template_coq.cmxa src/template_coq.cmxs build


plugin: coq Makefile.plugin gen-src/.generate
	@ echo "Copying from src to gen-src"
	@ for x in $(TOCOPY); do rm -f gen-src/$$x; cp src/$$x gen-src/$$x; done
	(cd gen-src; ./to-lower.sh)
	$(MAKE) -f Makefile.plugin

gen-src/.generate: theories/Extraction.vo theories/Extraction.v
	coqc -Q theories Template theories/Extraction.v
	@ touch gen-src/.generate


.PHONY: all install html clean mrproper plugin coq

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

TOCOPY=ast_denoter.ml ast_quoter.ml denote.ml denoter.ml plugin_core.ml plugin_core.mli quoted.ml quoter.ml run_extractable.ml run_extractable.mli tm_util.ml
