all: theory

_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin $(DEPS)

Makefile.pcuic: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.pcuic $(DEPS)

theory: Makefile.pcuic
	$(MAKE) -f Makefile.pcuic

plugin: theory Makefile.plugin
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.pcuic install
	$(MAKE) -f Makefile.plugin install

clean: Makefile.pcuic Makefile.plugin
	make -f Makefile.pcuic clean
	make -f Makefile.plugin clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.plugin _PluginProject
	rm -f Makefile.pcuic _CoqProject
