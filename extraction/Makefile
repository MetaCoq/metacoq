
all: theory plugin

_PluginProject: _PluginProject.in metacoq-config
	cat metacoq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin $(DEPS)

Makefile.extraction: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.extraction $(DEPS)

theory: Makefile.extraction
	$(MAKE) -f Makefile.extraction
	sh clean_extraction.sh

plugin: theory Makefile.plugin
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.extraction install
	$(MAKE) -f Makefile.plugin install

clean: Makefile.extraction Makefile.plugin
	make -f Makefile.extraction clean
	make -f Makefile.plugin clean

mrproper:
	rm -f Makefile.plugin
	rm -f Makefile.extraction
