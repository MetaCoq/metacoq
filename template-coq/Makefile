all: coq template-coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

# The template-coq plugin to run template programs live in Coq
template-coq: coq Makefile.template
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.template optfiles
	$(MAKE) -f Makefile.template

# The extractable template plugin to run *extracted* template programs in OCaml
# The sources of the plugin are built by the coq target, which calls the
# ./update_plugin.sh after successfull extraction.

plugin: coq template-coq Makefile.plugin
	$(MAKE) -f Makefile.plugin

.PHONY: install html clean mrproper all plugin

install: Makefile.coq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.template install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.coq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.coq uninstall
	$(MAKE) -f Makefile.template uninstall
	$(MAKE) -f Makefile.plugin uninstall

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
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.plugin/g Makefile.plugin > Makefile.plugin.tmp && mv -f Makefile.plugin.tmp Makefile.plugin

Makefile.template: _TemplateCoqProject
	coq_makefile -f _TemplateCoqProject -o Makefile.template
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.template/g Makefile.template > Makefile.template.tmp && mv -f Makefile.template.tmp Makefile.template

.merlin: Makefile.plugin
	[ -e "gen-src/signature.mli" ] && $(MAKE) -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
