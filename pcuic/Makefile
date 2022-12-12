all: theory # plugin

_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin $(DEPS)
	sed -e s/coqdeps/coqdeps.plugin/g Makefile.plugin > Makefile.plugin.tmp && mv -f Makefile.plugin.tmp Makefile.plugin

Makefile.pcuic: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.pcuic $(DEPS)

theory: Makefile.pcuic
	$(MAKE) -f Makefile.pcuic

plugin: theory Makefile.plugin
	$(MAKE) -f Makefile.plugin

install: theory # plugin
	$(MAKE) -f Makefile.pcuic install
	# $(MAKE) -f Makefile.plugin install

uninstall: Makefile.pcuic # Makefile.plugin
	$(MAKE) -f Makefile.pcuic uninstall
	# $(MAKE) -f Makefile.plugin uninstall

clean: Makefile.pcuic Makefile.plugin
	make -f Makefile.pcuic clean
	# make -f Makefile.plugin clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.plugin _PluginProject
	rm -f Makefile.pcuic _CoqProject

.merlin: Makefile.plugin
	[ -e "src/pCUICAst.ml" ] && make -f $< $@

cleanplugin: Makefile.plugin
#	make -f Makefile.plugin clean

vos: Makefile.pcuic
	$(MAKE) -f Makefile.pcuic vos

quick: Makefile.pcuic
	$(MAKE) -f Makefile.pcuic COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
