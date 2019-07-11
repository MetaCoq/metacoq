Anonymized artifact / supplementary material for POPL submission Coq Coq
Correct!

This archive contains the whole development as source. It can be
compiled with Coq 8.8.2 and Equations 1.2. If you don't have Coq
installed, the easiest way to get both is to use the `opam` package
manager. First install opam from your package manager 
(or using the instructions below) and then issue the command:

    # opam install coq.8.8.2 coq-equations.1.2+8.8
    
Then, to compile the sources, simply type:

    # ./configure.sh local
    # make

  - The `template-coq` directory contains the formalization of 
    the quoted language from Coq (with binary applications and casts)
    and some of its basic metatheory.
  - The `pcuic` directory contains the definition of PCUIC,
    along with its metatheory and a proof in TemplateToPCUICCorrectness
    of the correctness of the translation from Template-Coq to
    PCUIC (the translation itself is reduction-preserving).
    File `pcuic/theories/PCUICAdmittedLemmata.v` summarizes all the
    currently admitted subproofs in this study.
  - The `safechecker` directory contains the verified reduction,
    conversion and typechecking implementations and correctness proofs.
  - The `extraction` directory containa the verified erasure
    implementation.

# Installing opam

    # `curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh > install.sh`
    # sh install.sh --no-backup; opam init --disable-sandboxing
    
# Install from source

    tar zxf equations.tgz
    cd Coq-Equations-1.2-8.9
    coq_makefile -f _CoqProject -o Makefile
    make

in the toplevel directory, with `coqc` and `ocamlc` in your path.

Then install it:

    make install

Or add the paths to your `.coqrc`: 

    Add ML Path "PATH_TO_EQUATIONS/src".
    Add Rec LoadPath "PATH_TO_EQUATIONS/theories" as Equations.

As usual, you will need to run this command with the appropriate privileges
if the version of Coq you are using is installed system-wide, rather than
in your own directory. E.g. on Ubuntu, you would prefix the command with
`sudo` and then enter your user account password when prompted.

If this worked correctly, in `coqtop` the following should work:

    From Equations Require Import Equations.
