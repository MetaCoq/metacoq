all: theory plugin

_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin $(DEPS)
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.plugin/g Makefile.plugin > Makefile.plugin.tmp && mv -f Makefile.plugin.tmp Makefile.plugin

Makefile.erasureplugin: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.erasureplugin $(DEPS)

theory: Makefile.erasureplugin
	$(MAKE) -f Makefile.erasureplugin
	./clean_extraction.sh

plugin: theory Makefile.plugin
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.erasureplugin install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.erasureplugin Makefile.plugin
	$(MAKE) -f Makefile.erasureplugin uninstall
	$(MAKE) -f Makefile.plugin uninstall

clean: Makefile.erasureplugin Makefile.plugin
	make -f Makefile.erasureplugin clean
	make -f Makefile.plugin clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.plugin _PluginProject
	rm -f Makefile.erasureplugin _CoqProject

.merlin: Makefile.plugin
	[ -e "src/pCUICerasureplugin.ml" ] && make -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

vos: Makefile.erasureplugin
	$(MAKE) -f Makefile.erasureplugin vos

quick: Makefile.erasureplugin
	$(MAKE) -f Makefile.erasureplugin COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
