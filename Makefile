all: coq templatecoq templatecoqchecker

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.coqplugin install
	$(MAKE) -f Makefile.coqchecker install

clean: Makefile.coq Makefile.coqplugin Makefile.coqchecker
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.coqplugin clean
	$(MAKE) -f Makefile.coqchecker clean
	
mrproper: clean
	rm -f Makefile.coq Makefile.coqplugin Makefile.coqchecker
 
Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coqplugin: _CompilerProject
	coq_makefile -f _CompilerProject -o Makefile.coqplugin

.PHONY: coq

Makefile.coqchecker: _CheckerProject
	$(COQBIN)coq_makefile -f _CheckerProject -o Makefile.coqchecker

test-suite: coq
	$(MAKE) -C test-suite

templatecoq: coq Makefile.coqplugin
	$(COQBIN)coqc -I src -R theories Template theories/Extraction.v
	sh movefiles.sh
	$(MAKE) -f Makefile.coqplugin

.merlin: Makefile.coq
	make -f Makefile.coq .merlin

templatecoqchecker: coq templatecoq Makefile.coqchecker
	$(COQBIN)coqc -I src -R theories Template theories/TypingPlugin.v
	sh movefiles.sh
	$(MAKE) -f Makefile.coqchecker

translations: coq
	$(MAKE) -C translations
