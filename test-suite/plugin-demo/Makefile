TEMPLATE_LIB=../../template-coq

coq: sources Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject gen-src get-mc
	coq_makefile -f _CoqProject -o Makefile.coq

gen-src:
	$(MAKE) -C gen-src

get-mc:
	cp -r $(TEMPLATE_LIB)/gen-src/to-lower.sh src
	(cd src; ./to-lower.sh)
	cp -r $(TEMPLATE_LIB)/gen-src/*.ml $(TEMPLATE_LIB)/gen-src/*.mli src

.PHONY: get-mc gen-src

clean:
	$(MAKE) -f Makefile.coq clean

sources:
	$(MAKE) -C gen-src
