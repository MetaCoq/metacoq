SED = `which gsed || which sed`

all: coq template-coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

# The template-coq plugin to run template programs live in Coq
template-coq: coq Makefile.template
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.template optfiles
	cp src/template_coq.cm* build/
	$(MAKE) -f Makefile.template

# The extractable template plugin to run *extracted* template programs in OCaml
# The sources of the plugin are built by the coq target, which calls the
# ./update_plugin.sh after successfull extraction.

plugin: coq template-coq Makefile.plugin
	$(MAKE) -f Makefile.plugin

.PHONY: install html clean mrproper all plugin

install: Makefile.coq coq template-coq plugin
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.template install
	$(MAKE) -f Makefile.plugin install

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.template clean
	$(MAKE) -f Makefile.plugin clean
	rm -f build/*

mrproper:
	rm -f Makefile.coq
	rm -f Makefile.plugin
	rm -f Makefile.template

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin
# Avoid conflicting dependency file creation for the template plugin
	$(SED) -i -e s/coqdeps/coqdeps.plugin/g Makefile.plugin

Makefile.template: _TemplateCoqProject
	coq_makefile -f _TemplateCoqProject -o Makefile.template
# Avoid conflicting dependency file creation for the template plugin
	$(SED) -i -e s/coqdeps/coqdeps.template/g Makefile.template

.merlin: Makefile.coq
	$(MAKE) -f Makefile.plugin .merlin

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

TOCOPY=ast_denoter.ml ast_quoter.ml denote.ml denoter.ml plugin_core.ml plugin_core.mli quoted.ml quoter.ml run_extractable.ml run_extractable.mli tm_util.ml
