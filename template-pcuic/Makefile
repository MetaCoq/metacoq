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

Makefile.templatepcuic: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.templatepcuic $(DEPS)

theory: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic
	./clean_extraction.sh

plugin: theory Makefile.plugin
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.templatepcuic install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.templatepcuic Makefile.plugin
	$(MAKE) -f Makefile.templatepcuic uninstall
	$(MAKE) -f Makefile.plugin uninstall

clean: Makefile.templatepcuic Makefile.plugin
	make -f Makefile.templatepcuic clean
	make -f Makefile.plugin clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.plugin _PluginProject
	rm -f Makefile.templatepcuic _CoqProject

.merlin: Makefile.plugin
	[ -e "src/pCUICtemplatepcuic.ml" ] && make -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

vos: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic vos

quick: Makefile.templatepcuic
	$(MAKE) -f Makefile.templatepcuic COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
