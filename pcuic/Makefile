
all: theory plugin

Makefile.plugin:
	coq_makefile -f _PluginProject -o Makefile.plugin

Makefile.pcuic:
	coq_makefile -f _CoqProject -o Makefile.pcuic

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
	rm -f Makefile.plugin
	rm -f Makefile.pcuic
