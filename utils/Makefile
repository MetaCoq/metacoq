all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: install html clean mrproper all plugin

install: Makefile.coq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.template install
	$(MAKE) -f Makefile.plugin install

uninstall: Makefile.coq Makefile.template Makefile.plugin
	$(MAKE) -f Makefile.coq uninstall
	$(MAKE) -f Makefile.template uninstall
	$(MAKE) -f Makefile.plugin uninstall

html: all
	$(MAKE) -f Makefile.coq html

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.template clean
	$(MAKE) -f Makefile.plugin clean

mrproper:
	rm -f Makefile.coq
	rm -f Makefile.plugin
	rm -f Makefile.template

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.merlin: Makefile.plugin
	[ -e "gen-src/signature.mli" ] && $(MAKE) -f $< $@

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
