all: template-coq checker extraction

.PHONY: all template-coq checker install html clean mrproper .merlin test-suite translations

install: 
	$(MAKE) -C template-coq install
	$(MAKE) -C checker install
	$(MAKE) -C extraction install

html: all
	$(MAKE) -C template-coq html
	$(MAKE) -C extraction html
	mv template-coq/html/*.html html
	rm template-coq/html/coqdoc.css
	rm -d template-coq/html

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C extraction clean
	$(MAKE) -C checker clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C extraction mrproper
	$(MAKE) -C checker mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C checker .merlin

template-coq:
	$(MAKE) -C template-coq

extraction: template-coq
	$(MAKE) -C extraction

checker: template-coq
	./movefiles.sh
	$(MAKE) -C checker

test-suite: template-coq checker
	$(MAKE) -C test-suite

translations: template-coq
	$(MAKE) -C translations
