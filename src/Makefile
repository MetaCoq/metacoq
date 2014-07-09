OCAMLBUILDDIR=$(shell ocamlfind query ocamlbuild)

all: myocamlbuild.ml
	ocamlbuild coq.otarget

myocamlbuild.ml: ../myocamlbuild.template
	@ echo 'let coq_config_string = "'`coqc -config | tr '\n' '|'`'";; ' > myocamlbuild.ml
	@ echo >> myocamlbuild.ml
	@ cat ../myocamlbuild.template >> myocamlbuild.ml

clean:
	@ ocamlbuild -clean
	@ rm -f myocamlbuild.ml
