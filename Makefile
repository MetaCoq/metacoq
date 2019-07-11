all: template-coq pcuic safechecker extraction

.PHONY: all template-coq pcuic extraction install html clean mrproper .merlin test-suite

install:
	$(MAKE) -C template-coq install
	$(MAKE) -C pcuic install
	$(MAKE) -C safechecker install
	$(MAKE) -C extraction install

html: all
	"coqdoc" -toc -utf8 -interpolate -l -html \
		-R template-coq/theories MetaCoq.Template \
		-R pcuic/theories MetaCoq.PCUIC \
		-R safechecker/theories MetaCoq.SafeChecker \
		-R extraction/theories MetaCoq.Extraction \
		-d html */theories/*.v

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C pcuic clean
	$(MAKE) -C safechecker clean
	$(MAKE) -C extraction clean
	$(MAKE) -C test-suite clean

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C pcuic mrproper
	$(MAKE) -C safechecker mrproper
	$(MAKE) -C extraction mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C pcuic .merlin
	$(MAKE) -C safechecker .merlin
	$(MAKE) -C extraction .merlin

template-coq:
	$(MAKE) -C template-coq

pcuic: template-coq
	$(MAKE) -C pcuic

safechecker: template-coq pcuic
	$(MAKE) -C safechecker

extraction: template-coq safechecker pcuic
	$(MAKE) -C extraction

test-suite: template-coq
	$(MAKE) -C test-suite
