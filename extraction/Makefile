
all: theory plugin

Makefile.plugin:
	coq_makefile -f _PluginProject -o Makefile.plugin

Makefile.extraction:
	coq_makefile -f _CoqProject -o Makefile.extraction

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
