all: template-coq checker

.PHONY: all template-coq checker install html clean mrproper

install: 
	$(MAKE) -C template-coq install
	$(MAKE) -C checker install

html: all
	$(MAKE) -C template-coq html
	$(MAKE) -C checker html
#	git checkout html/coqdoc.css # Preserve custom coqdoc

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C checker clean
# git checkout html/coqdoc.css

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C checker mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C checker .merlin

template-coq:
	$(MAKE) -C template-coq

checker: template-coq
	./movefiles.sh
	$(MAKE) -C checker
