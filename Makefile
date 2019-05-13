all: template-coq checker pcuic extraction

.PHONY: all template-coq checker install html clean mrproper .merlin test-suite translations

install:
	$(MAKE) -C template-coq install
	$(MAKE) -C checker install
	$(MAKE) -C pcuic install
	$(MAKE) -C extraction install

html: all
	$(MAKE) -C template-coq html
	$(MAKE) -C pcuic html
	$(MAKE) -C extraction html
	mv template-coq/html/*.html html
	rm template-coq/html/coqdoc.css
	rm -d template-coq/html

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C pcuic clean
	$(MAKE) -C extraction clean
	$(MAKE) -C checker clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C pcuic mrproper
	$(MAKE) -C extraction mrproper
	$(MAKE) -C checker mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C pcuic .merlin
	$(MAKE) -C extraction .merlin
	$(MAKE) -C checker .merlin

template-coq:
	$(MAKE) -C template-coq

pcuic: template-coq
	$(MAKE) -C pcuic

extraction: checker template-coq pcuic
	$(MAKE) -C extraction

checker: template-coq
	./movefiles.sh
	$(MAKE) -C checker

test-suite: template-coq checker
	$(MAKE) -C test-suite

translations: template-coq
	$(MAKE) -C translations
