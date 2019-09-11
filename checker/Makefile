all: coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin

plugin: Makefile.plugin coq
	$(MAKE) -f Makefile.plugin

install: coq plugin
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.plugin install

.PHONY: plugin

clean: Makefile.coq Makefile.plugin
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.plugin clean

mrproper:
	rm -f Makefile.coq Makefile.plugin _CoqProject _PluginProject

.merlin:
	make -f Makefile.plugin .merlin

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
