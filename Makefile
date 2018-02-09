COMPILER := theories/TemplateCoqCompiler.vo
CHECKER := theories/TemplateCoqChecker.vo

all: makefiles coq $(COMPILER) $(CHEKER)

.PHONY: all makefiles coq translations install test-suite html clean

makefiles: Makefile.coq Makefile.coqplugin Makefile.coqchecker

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install
	$(MAKE) -f Makefile.coqplugin install
	$(MAKE) -f Makefile.coqchecker install

html: all
	$(MAKE) -f Makefile.coq html
	$(MAKE) -f Makefile.coqplugin html
	$(MAKE) -f Makefile.coqchecker html
	git checkout html/coqdoc.css # Preserve custom coqdoc

clean: Makefile.coq Makefile.coqplugin Makefile.coqchecker
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.coqplugin clean
	$(MAKE) -f Makefile.coqchecker clean

mrproper: clean
	rm -f Makefile.coq Makefile.coqplugin Makefile.coqchecker

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.coqplugin: _CompilerProject
	coq_makefile -f _CompilerProject -o Makefile.coqplugin

Makefile.coqchecker: _CheckerProject
	coq_makefile -f _CheckerProject -o Makefile.coqchecker

test-suite: coq
	$(MAKE) -C test-suite

theories/TemplateCoqCompiler.vo: Makefile.coqplugin theories/Extraction.v theories/TemplateCoqCompiler.v | coq
	$(COQBIN)coqc -I src -R theories Template theories/Extraction.v
	sh movefiles.sh
	$(MAKE) -f Makefile.coqplugin

.merlin: Makefile.coq
	make -f Makefile.coq .merlin

theories/TemplateCoqChecker.vo: Makefile.coqchecker $(COMPILER) theories/TypingPlugin.v | theories/TemplateCoqCompiler.vo
	$(COQBIN)coqc -I src -R theories Template theories/TypingPlugin.v
	sh movefiles.sh
	$(MAKE) -f Makefile.coqchecker

translations:
	$(MAKE) -C translations
