coq: Makefile.coq
	$(MAKE) -f Makefile.coq


install: Makefile.coq
	$(MAKE) -f Makefile.coq install
	# sudo cp src/template_plugin.cmxs /usr/local/lib/coq/user-contrib/Template/ #FIX, this is currently needed but should not be. why does make install say that it skipped these files

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

test-suite: coq
	$(MAKE) -C test-suite
