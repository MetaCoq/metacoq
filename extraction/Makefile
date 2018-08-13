
all: theory plugin

Makefile.plugin:
	coq_makefile -f _PluginProject -o Makefile.plugin

Makefile.extraction:
	coq_makefile -f _CoqProject -o Makefile.extraction

theory: Makefile.extraction
	make -f	Makefile.extraction
	sh clean_extraction.sh

plugin: theory Makefile.plugin
	make -f	Makefile.plugin

install: theory plugin
	make -f Makefile.extraction install
	make -f Makefile.plugin install

clean: Makefile.extraction Makefile.plugin
	make -f Makefile.extraction clean
	make -f Makefile.plugin clean
