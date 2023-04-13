
all: printconf template-coq pcuic safechecker erasure examples test-suite translations quotation

-include Makefile.conf

ifeq '$(METACOQ_CONFIG)' 'local'
  ifeq ($(shell which cygpath 2>/dev/null),)
  OCAMLPATH := $(shell pwd)/template-coq/:$(OCAMLPATH)
  else
  OCAMLPATH := $(shell cygpath -m `pwd`)/template-coq/;$(OCAMLPATH)
  endif
  export OCAMLPATH
endif

.PHONY: printconf all utils template-coq pcuic erasure install uninstall html clean mrproper .merlin test-suite translations quotation

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
	$(MAKE) -C utils install
	$(MAKE) -C common install
	$(MAKE) -C template-coq install
	$(MAKE) -C pcuic install
	$(MAKE) -C safechecker install
	$(MAKE) -C template-pcuic install
	$(MAKE) -C quotation install
	$(MAKE) -C safechecker-plugin install
	$(MAKE) -C erasure install
	$(MAKE) -C translations install

uninstall:
	$(MAKE) -C utils uninstall
	$(MAKE) -C common uninstall
	$(MAKE) -C template-coq uninstall
	$(MAKE) -C pcuic uninstall
	$(MAKE) -C safechecker uninstall
	$(MAKE) -C template-pcuic uninstall
	$(MAKE) -C quotation uninstall
	$(MAKE) -C safechecker-plugin uninstall
	$(MAKE) -C erasure uninstall
	$(MAKE) -C translations uninstall

html: all
	"coqdoc" --multi-index -toc -utf8 -html \
    --with-header ./html/resources/header.html --with-footer ./html/resources/footer.html \
		-R utils/theories MetaCoq.Utils \
		-R common/theories MetaCoq.Common \
		-R template-coq/theories MetaCoq.Template \
		-R pcuic/theories MetaCoq.PCUIC \
		-R safechecker/theories MetaCoq.SafeChecker \
		-R template-pcuic/theories MetaCoq.TemplatePCUIC \
		-R quotation/theories MetaCoq.Quotation \
		-R erasure/theories MetaCoq.Erasure \
		-R erasure-plugin/theories MetaCoq.ErasurePlugin \
		-R translations MetaCoq.Translations \
		-R examples MetaCoq.Examples \
		-d html */theories/*.v */theories/*/*.v translations/*.v examples/*.v

clean:
	$(MAKE) -C utils clean
	$(MAKE) -C common clean
	$(MAKE) -C template-coq clean
	$(MAKE) -C pcuic clean
	$(MAKE) -C safechecker clean
	$(MAKE) -C template-pcuic clean
	$(MAKE) -C quotation clean
	$(MAKE) -C erasure clean
	$(MAKE) -C erasure-plugin clean
	$(MAKE) -C examples clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

vos:
	$(MAKE) -C utils
	$(MAKE) -C common
	$(MAKE) -C template-coq
	$(MAKE) -C pcuic vos
	$(MAKE) -C safechecker vos
	$(MAKE) -C template-pcuic vos
	$(MAKE) -C quotation vos
	$(MAKE) -C erasure vos
	$(MAKE) -C erasure-plugin vos
	$(MAKE) -C translations vos

quick:
	$(MAKE) -C utils
	$(MAKE) -C common
	$(MAKE) -C template-coq
	$(MAKE) -C pcuic quick
	$(MAKE) -C safechecker quick
	$(MAKE) -C template-pcuic quick
	$(MAKE) -C quotation # quick # we cannot unset universe checking in 8.16 due to COQBUG(https://github.com/coq/coq/issues/17361), and quick does not buy much in quotation anyway, where almost everything is transparent
	$(MAKE) -C erasure quick
	$(MAKE) -C erasure-plugin quick
	$(MAKE) -C translations quick

mrproper:
	$(MAKE) -C utils mrproper
	$(MAKE) -C common mrproper
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C pcuic mrproper
	$(MAKE) -C safechecker mrproper
	$(MAKE) -C template-pcuic mrproper
	$(MAKE) -C quotation mrproper
	$(MAKE) -C erasure mrproper
	$(MAKE) -C erasure-plugin mrproper
	$(MAKE) -C examples mrproper
	$(MAKE) -C test-suite mrproper
	$(MAKE) -C translations mrproper

.merlin:
	$(MAKE) -C utils .merlin
	$(MAKE) -C common .merlin
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C pcuic .merlin
	$(MAKE) -C safechecker .merlin
	$(MAKE) -C template-pcuic .merlin
	$(MAKE) -C quotation .merlin
	$(MAKE) -C erasure .merlin
	$(MAKE) -C erasure-plugin .merin

utils:
	$(MAKE) -C utils

common: utils
	$(MAKE) -C common

template-coq: common
	$(MAKE) -C template-coq

pcuic: common
	$(MAKE) -C pcuic

safechecker: pcuic
	$(MAKE) -C safechecker

template-pcuic: template-coq pcuic
	$(MAKE) -C template-pcuic

quotation: template-coq # pcuic template-pcuic
	$(MAKE) -C quotation

safechecker-plugin: safechecker template-pcuic
	$(MAKE) -C safechecker-plugin

erasure: safechecker template-pcuic
	$(MAKE) -C erasure

erasure-plugin: erasure template-pcuic
	$(MAKE) -C erasure-plugin

examples: safechecker-plugin erasure-plugin
	$(MAKE) -C examples

test-suite: safechecker-plugin erasure-plugin
	$(MAKE) -C test-suite

translations: template-coq
	$(MAKE) -C translations

cleanplugins:
	$(MAKE) -C template-coq cleanplugin
	$(MAKE) -C safechecker-plugin cleanplugin
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
	opam install --with-test -v -y .
	opam remove -y coq-metacoq coq-metacoq-template

checktodos:
	sh checktodos.sh
