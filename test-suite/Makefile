all: bugs plugin-demo

bugs: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

plugin-demo: template-coq
	$(MAKE) -C plugin-demo
