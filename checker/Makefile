# Explicitly use GNU sed on OS X
SED=`which gsed || which sed`
TEMPLATE_LIB=../template-coq

coq: sources Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: get-mc
	echo "-Q ../template-coq/theories MetaCoq.Template" > _CoqProject
	echo "-I ../template-coq/gen-src" >> _CoqProject
	echo "-I src" >> _CoqProject
	echo "-R theories MetaCoq.Checker" >> _CoqProject
	echo "" >> _CoqProject
	ocamldep -sort src/*.ml | $(SED) -e "s+ +\n+g" | $(SED) -e "s+\(src/.*.ml\)+\1\n\1i+g" >> _CoqProject
	echo "src/metacoq_checker_plugin.mlpack" >> _CoqProject
	echo "src/g_metacoq_checker.ml4" >> _CoqProject
	echo "" >> _CoqProject
	echo "theories/Loader.v" >> _CoqProject

gen-src:
	$(MAKE) -C gen-src

get-mc: gen-src
	cp -r $(TEMPLATE_LIB)/gen-src/to-lower.sh src
	(cd src; ./to-lower.sh)

install:
	$(MAKE) -f Makefile.coq install

.PHONY: get-mc gen-src

clean:
	$(MAKE) -f Makefile.coq clean

mrproper: clean
	rm -f Makefile.coq

sources: gen-src
