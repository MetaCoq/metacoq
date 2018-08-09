
all: theory plugin

theory:
	coq_makefile -f _CoqProject -o Makefile.extraction
	make -f	Makefile.extraction
	sh clean_extraction.sh

plugin:
	coq_makefile -f _PluginProject -o Makefile.plugin
	make -f	Makefile.plugin

install:
	make -f Makefile.extraction install
	make -f Makefile.plugin install

clean:
	make -f Makefile.extraction clean
	make -f Makefile.plugin clean
