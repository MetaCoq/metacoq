SED = `which gsed || which sed`

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
	$(SED) -i -e s/coqdeps/coqdeps.plugin/g Makefile.plugin

Makefile.safechecker: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.safechecker $(DEPS)

theory: Makefile.safechecker
	$(MAKE) -f Makefile.safechecker

plugin: theory Makefile.plugin
# Force building the ML code before the .v's requiring them.
	$(MAKE) -f Makefile.plugin

install: theory plugin
	$(MAKE) -f Makefile.safechecker install
	$(MAKE) -f Makefile.plugin install

clean: Makefile.safechecker Makefile.plugin
	make -f Makefile.safechecker clean
	make -f Makefile.plugin clean

mrproper:
	rm -f metacoq-config
	rm -f Makefile.plugin _PluginProject
	rm -f Makefile.safechecker _CoqProject

.merlin:
	make -f Makefile.plugin .merlin

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
