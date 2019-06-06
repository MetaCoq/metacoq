with import <nixpkgs> {};

stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq_8_8 ]
    ++ (with ocamlPackages; [ findlib camlp5 ])
    ++ (with coqPackages_8_8; [ mathcomp-ssreflect ]);
}
