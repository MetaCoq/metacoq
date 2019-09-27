all: template-coq checker pcuic safechecker erasure

.PHONY: all template-coq checker pcuic erasure install html clean mrproper .merlin test-suite translations

install: all
	$(MAKE) -C template-coq install
	$(MAKE) -C checker install
	$(MAKE) -C pcuic install
	$(MAKE) -C safechecker install
	$(MAKE) -C erasure install
	$(MAKE) -C translations install

html: all
	"coqdoc" -toc -utf8 -interpolate -l -html \
		-R template-coq/theories MetaCoq.Template \
		-R checker/theories MetaCoq.Checker \
		-R pcuic/theories MetaCoq.PCUIC \
		-R safechecker/theories MetaCoq.SafeChecker \
		-R erasure/theories MetaCoq.Erasure \
		-R translations MetaCoq.Translations \
		-d html */theories/*.v translations/*.v

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C checker clean
	$(MAKE) -C pcuic clean
	$(MAKE) -C safechecker clean
	$(MAKE) -C erasure clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C pcuic mrproper
	$(MAKE) -C safechecker mrproper
	$(MAKE) -C erasure mrproper
	$(MAKE) -C checker mrproper
	$(MAKE) -C test-suite mrproper
	$(MAKE) -C translations mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C pcuic .merlin
	$(MAKE) -C safechecker .merlin
	$(MAKE) -C erasure .merlin
	$(MAKE) -C checker .merlin

template-coq:
	$(MAKE) -C template-coq

pcuic: template-coq checker
	$(MAKE) -C pcuic

safechecker: template-coq checker pcuic
	$(MAKE) -C safechecker

erasure: template-coq safechecker pcuic
	$(MAKE) -C erasure

checker: template-coq
	$(MAKE) -C checker

test-suite: template-coq checker safechecker erasure
	$(MAKE) -C test-suite

translations: template-coq checker
	$(MAKE) -C translations

cleanplugins:
	$(MAKE) -C template-coq cleanplugin
	$(MAKE) -C pcuic cleanplugin
	$(MAKE) -C checker cleanplugin
	$(MAKE) -C safechecker cleanplugin
	$(MAKE) -C erasure cleanplugin

ci-local:
	./configure.sh local
	$(MAKE) all test-suite

ci-opam:
	opam install -y .
