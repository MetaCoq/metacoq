all: coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	cd gen-src && ./to-lower.sh

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject
	
_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

plugin: Makefile.plugin coq
	$(MAKE) -f Makefile.plugin

.PHONY: plugin

clean: Makefile.coq Makefile.plugin
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.plugin clean

.merlin:
	make -f Makefile.plugin .merlin

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
