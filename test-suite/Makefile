.PHONY: all bugd clean mrproper plugin-demo

all: bugs plugin-demo

bugs: Makefile.coq
	$(MAKE) -f Makefile.coq TIMED=$(TIMED)

Makefile.coq: Makefile _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

_CoqProject: _CoqProject.in metacoq-config
	cat metacoq-config > _CoqProject
	cat _CoqProject.in >> _CoqProject

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

mrproper:
	rm -f Makefile.coq

plugin-demo:
	$(MAKE) -C plugin-demo

vos: Makefile.coq
	$(MAKE) -f Makefile.coq vos

quick: Makefile.coq
	$(MAKE) -f Makefile.coq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos

TEST_SUITE_BLACKLIST := \
	TypeAnnotationTests.v \
	CheckerTest.v \
	ErasureTests.v \
	self_erasure.v \
	primitive.v \
	plugin-demo/.*.v \
	#

space := $(subst ,, )

TEST_SUITE_BLACKLIST_SED:=\($(subst $(space),\|,$(strip $(TEST_SUITE_BLACKLIST)))\)

.PHONY: update-_CoqProject.in
update-_CoqProject.in:
	{ printf '%s\n\n%s\n\n' '-R . MetaCoq.TestSuite' '# list obtained with `git ls-files "*.v"`'; \
	  { git ls-files "*.v" || ls -1 *.v; } | env LC_COLLATE=C sort | sed 's,^$(TEST_SUITE_BLACKLIST_SED)$$,# \1,g'; \
	} > _CoqProject.in
