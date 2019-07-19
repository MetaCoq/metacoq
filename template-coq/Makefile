all: coq template-coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

# The template-coq plugin to run template programs live in Coq
template-coq: coq Makefile.template
	$(MAKE) -f Makefile.template optfiles
	$(MAKE) -f Makefile.template all

# The extractable template plugin to run *extracted* template programs in OCaml
# The sources of the plugin are built by the coq target, which calls the
# ./update_plugin.sh after successfull extraction.

plugin: coq template-coq Makefile.plugin
	$(MAKE) -f Makefile.plugin

.PHONY: install html clean mrproper all plugin

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.template clean
	$(MAKE) -f Makefile.plugin clean

mrproper:
	rm -f Makefile.coq
	rm -f Makefile.plugin
	rm -f Makefile.template

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin

Makefile.template: _TemplateCoqProject
	coq_makefile -f _TemplateCoqProject -o Makefile.template

x.merlin: Makefile.coq
	$(MAKE) -f Makefile.coq .merlin

TOCOPY=ast_denoter.ml ast_quoter.ml denote.ml denoter.ml plugin_core.ml plugin_core.mli quoted.ml quoter.ml run_extractable.ml run_extractable.mli tm_util.ml
