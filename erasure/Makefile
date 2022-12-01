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

Makefile.erasure: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.erasure $(DEPS)

theory: Makefile.erasure
	$(MAKE) -f Makefile.erasure
	./clean_extraction.sh

plugin: theory Makefile.plugin
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.erasure install
	$(MAKE) -f Makefile.plugin install

uninstall: theory plugin
	$(MAKE) -f Makefile.erasure uninstall
	$(MAKE) -f Makefile.plugin uninstall

clean: Makefile.erasure Makefile.plugin
	make -f Makefile.erasure clean
	make -f Makefile.plugin clean

mrproper:
	rm -f Makefile.plugin
	rm -f Makefile.erasure

.merlin: Makefile.plugin
	[ -e "src/erasureFunction.ml" ] && make -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean

vos: Makefile.erasure
	$(MAKE) -f Makefile.erasure vos

quick: Makefile.erasure
	$(MAKE) -f Makefile.erasure COQEXTRAFLAGS="-unset \"Universe Checking\"" vos
