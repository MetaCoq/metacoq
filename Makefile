###############################################################################
##  v      #                   The Coq Proof Assistant                       ##
## <O___,, #                INRIA - CNRS - LIX - LRI - PPS                   ##
##   \VV/  #                                                                 ##
##    //   #                                                                 ##
###############################################################################
## GNUMakefile for Coq 8.7.1

install: Makefile.coq templatecoq
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.coqplugin install

clean: Makefile.coq Makefile.coqplugin
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.coqplugin clean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coqplugin: _CompilerProject
	coq_makefile -f _CompilerProject -o Makefile.coqplugin

coq:
	$(MAKE) -f Makefile.coq

.PHONY: coq

test-suite: coq
	$(MAKE) -C test-suite

templatecoq: coq Makefile.coqplugin
	$(COQBIN)coqc -R theories Template theories/Extraction.v
	sh movefiles.sh
	$(MAKE) -f Makefile.coqplugin

.merlin: Makefile.coq
	make -f Makefile.coq .merlin
