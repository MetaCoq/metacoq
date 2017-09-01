coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq templatecoq
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.coqplugin install

clean: Makefile.coq Makefile.coqplugin
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.coqplugin clean

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coqplugin: _CompilerProject
	$(COQBIN)coq_makefile -f _CompilerProject -o Makefile.coqplugin

test-suite: coq
	$(MAKE) -C test-suite

templatecoq: coq Makefile.coqplugin
	$(COQBIN)coqc -R theories Template theories/Extraction.v
	sh movefiles.sh
	$(MAKE) -f Makefile.coqplugin
