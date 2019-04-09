TEMPLATE_LIB=../template-coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject gen-src get-mc
	coq_makefile -f _CoqProject -o Makefile.coq

gen-src:
	$(MAKE) -C gen-src

get-mc:
	cp -r $(TEMPLATE_LIB)/src/*.ml $(TEMPLATE_LIB)/src/*.mli src
	(cd src; ./movefiles.sh)

.PHONY: get-mc gen-src

clean:
	$(MAKE) -f Makefile.coq clean
