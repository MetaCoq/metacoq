all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: install html clean mrproper all plugin

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

.merlin: Makefile.coq
	$(MAKE) -f $< $@
