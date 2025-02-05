all: theory plugin

_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.plugin: _PluginProject
	rocq makefile -f _PluginProject -o Makefile.plugin $(DEPS)
# Avoid conflicting dependency file creation for the template plugin
	sed -e s/coqdeps/coqdeps.plugin/g Makefile.plugin > Makefile.plugin.tmp && mv -f Makefile.plugin.tmp Makefile.plugin

Makefile.safecheckerplugin: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.safecheckerplugin $(DEPS)

theory: Makefile.safecheckerplugin
	$(MAKE) -f Makefile.safecheckerplugin
	./clean_extraction.sh

plugin: theory Makefile.plugin
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.safecheckerplugin install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.safecheckerplugin Makefile.plugin
	$(MAKE) -f Makefile.safecheckerplugin uninstall
	$(MAKE) -f Makefile.plugin uninstall

clean: Makefile.safecheckerplugin Makefile.plugin
	make -f Makefile.safecheckerplugin clean
	make -f Makefile.plugin clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.plugin _PluginProject
	rm -f Makefile.safecheckerplugin _CoqProject

.merlin: Makefile.plugin
	make -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

vos: Makefile.safecheckerplugin
	$(MAKE) -f Makefile.safecheckerplugin vos

quick: Makefile.safecheckerplugin
	$(MAKE) -f Makefile.safecheckerplugin COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
