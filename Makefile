all: template-coq checker

.PHONY: all template-coq checker install html clean mrproper .merlin test-suite translations

install: 
	$(MAKE) -C template-coq install
	$(MAKE) -C checker install

html: all
	$(MAKE) -C template-coq html
	mv template-coq/html/*.html html
	rm template-coq/html/coqdoc.css
	rm -d template-coq/html

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C checker clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C checker mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C checker .merlin

template-coq:
	$(MAKE) -C template-coq

checker: template-coq
	./movefiles.sh
	$(MAKE) -C checker

test-suite: template-coq checker
	$(MAKE) -C test-suite

translations: template-coq
	$(MAKE) -C translations
