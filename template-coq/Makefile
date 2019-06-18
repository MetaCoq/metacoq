all: coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

plugin: coq Makefile.plugin theories/Extraction.vo
	sh update_plugin.sh
	$(MAKE) -f Makefile.plugin

.PHONY: install html clean mrproper all plugin

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq
	rm -f Makefile.plugin

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin

.merlin: Makefile.coq
	$(MAKE) -f Makefile.coq .merlin

TOCOPY=ast_denoter.ml ast_quoter.ml denote.ml denoter.ml plugin_core.ml plugin_core.mli quoted.ml quoter.ml run_extractable.ml run_extractable.mli tm_util.ml
