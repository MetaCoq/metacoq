Supplementary material for POPL submission Coq Coq Correct!

This archive contains the whole development as source (from 
https://github.com/MetaCoq/metacoq/tree/clean). If you only want
to browse the files a "light" documentation is available in
`html/toc.html` which provides access to all the development files
(it can be rebuilt with `make html`, not available through `opam` yet).

Otherwise, to run interactively, the development can be compiled with
Coq 8.8.2 and Equations 1.2. If you don't have Coq installed, the
easiest way to get both is to use the `opam` package manager. First
install `opam` from your package manager (or using the instructions below)
and then issue the command at the root of the directory:

    # opam install .
    
This should install Coq 8.8.2, Equations 1.2 and all the MetaCoq
packages. 

BEWARE: remove any previous installation of MetaCoq in `coqc
-where`/user-contrib before trying to compile anything, otherwise Coq 
might get confused as to which MetaCoq we are referring to.

Alternatively, to build locally you can first install Coq and Equations:

    # opam install coq.8.8.2 coq-equations.1.2+8.8

Then, to compile the sources, simply type:

    # ./configure.sh local
    # make
    
You can optionally install it using

    # make install

And build the doc with

    # make html

  - The `template-coq` directory contains the formalization of 
    the quoted language from Coq and the Template Monad from 
    the original MetaCoq project.
    
  - The `checker` directory contains some metatheory of the
    template-coq system (with n-ary applications and casts) including
    typing. Appart from the typing specification, this part has
    no links to the current paper.
  
  - The `pcuic` directory contains the definition of PCUIC,
    along with its metatheory and a proof in `TemplateToPCUICCorrectness`
    of the correctness of the translation from Template-Coq to
    PCUIC (the translation itself is reduction-preserving).
    File `pcuic/theories/PCUICAdmittedLemmata.v` summarizes all the
    currently admitted subproofs in this study.

  - The `safechecker` directory contains the verified reduction,
    conversion and typechecking implementations and correctness proofs.

  - The `erasure` directory contains the verified erasure
    implementation.

  - The `test-suite` directory contains test files for the extracted 
    checker and erasure functions in files `safechecker_test.v` and 
    `erasure_test.v` respectively. They can be run only after 
    MetaCoq has been built.

# Installing opam

    # `curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh > install.sh`
    # sh install.sh --no-backup; opam init --disable-sandboxing
