TESTS:=demo bug1 bug2 bug3 opaque
ARGS:=-I ../src -R ../theories Template

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile
	coq_makefile -o Makefile.coq  $(ARGS) $(TESTS:%=%.v)
