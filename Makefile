coq: Makefile.plugin.coq Makefile.coq
	$(MAKE) -f Makefile.plugin.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.plugin.coq install
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq Makefile.plugin.coq
	$(MAKE) -f Makefile.plugin.coq clean
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.plugin.coq Makefile.coq

Makefile.plugin.coq: _CoqProject
	coq_makefile src/reify.ml4 src/template_plugin.mlpack -o Makefile.plugin.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
