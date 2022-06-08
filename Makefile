
all: template-coq pcuic safechecker erasure examples test-suite translations

-include Makefile.conf

ifeq '$(METACOQ_CONFIG)' 'local'
  ifeq ($(shell which cygpath 2>/dev/null),)
  OCAMLPATH := $(shell pwd)/template-coq/:$(OCAMLPATH)
  else
  OCAMLPATH := $(shell cygpath -m `pwd`)/template-coq/;$(OCAMLPATH)
  endif
  export OCAMLPATH
endif

all: printconf template-coq pcuic safechecker erasure examples

.PHONY: printconf all template-coq pcuic erasure install html clean mrproper .merlin test-suite translations

printconf:
ifeq '$(METACOQ_CONFIG)' 'local'
	@echo "Local configuration"
else
ifeq '$(METACOQ_CONFIG)' 'global'
	@echo "Global configuration"
else
	@echo "Run ./configure.sh first"
	@exit 1
endif
endif

install: all translations
	$(MAKE) -C template-coq install
	$(MAKE) -C pcuic install
	$(MAKE) -C safechecker install
	$(MAKE) -C erasure install
	$(MAKE) -C translations install

uninstall: all
	$(MAKE) -C template-coq uninstall
	$(MAKE) -C pcuic uninstall
	$(MAKE) -C safechecker uninstall
	$(MAKE) -C erasure uninstall
	$(MAKE) -C translations uninstall

html: all
	"coqdoc" -toc -utf8 -interpolate -l -html \
		-R template-coq/theories MetaCoq.Template \
		-R pcuic/theories MetaCoq.PCUIC \
		-R safechecker/theories MetaCoq.SafeChecker \
		-R erasure/theories MetaCoq.Erasure \
		-R translations MetaCoq.Translations \
		-d html */theories/*.v translations/*.v

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C pcuic clean
	$(MAKE) -C safechecker clean
	$(MAKE) -C erasure clean
	$(MAKE) -C examples clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

vos:
	$(MAKE) -C template-coq
	$(MAKE) -C pcuic vos
	$(MAKE) -C safechecker vos
	$(MAKE) -C erasure vos
	$(MAKE) -C translations vos

quick:
	$(MAKE) -C template-coq
	$(MAKE) -C pcuic quick 
	$(MAKE) -C safechecker quick
	$(MAKE) -C erasure quick
	$(MAKE) -C translations quick

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C pcuic mrproper
	$(MAKE) -C safechecker mrproper
	$(MAKE) -C erasure mrproper
	$(MAKE) -C examples mrproper
	$(MAKE) -C test-suite mrproper
	$(MAKE) -C translations mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C pcuic .merlin
	$(MAKE) -C safechecker .merlin
	$(MAKE) -C erasure .merlin

template-coq:
	$(MAKE) -C template-coq

pcuic: template-coq
	$(MAKE) -C pcuic

safechecker: template-coq pcuic
	$(MAKE) -C safechecker

erasure: template-coq safechecker pcuic
	$(MAKE) -C erasure

examples: safechecker erasure
	$(MAKE) -C examples

test-suite: template-coq safechecker erasure
	$(MAKE) -C test-suite

translations: template-coq
	$(MAKE) -C translations

cleanplugins:
	$(MAKE) -C template-coq cleanplugin
	$(MAKE) -C safechecker cleanplugin
	$(MAKE) -C erasure cleanplugin

ci-local-noclean:
	./configure.sh local
	$(MAKE) all test-suite TIMED=pretty-timed

ci-local: ci-local-noclean
	$(MAKE) clean

ci-quick:
	./configure.sh --enable-quick
	time $(MAKE) quick TIMED=pretty-timed

ci-opam:
# Use -v so that regular output is produced
	opam install -v -y .
	opam remove -y coq-metacoq coq-metacoq-template
