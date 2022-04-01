{ pkgs ? import <nixpkgs> {},
  coqPackages ? pkgs.coqPackages_8_14 }:
let
  ocamlPackages = coqPackages.coq.ocamlPackages;
  metacoq = (import ./default.nix {}).metacoq;
  deps = {
    inherit (ocamlPackages) zarith;
    inherit (coqPackages) coq equations mkCoqDerivation;
    inherit (metacoq) template pcuic;
    inherit (pkgs) which;
  };
in
with deps;
let
  templateBuild = "-I ${template}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/Template/";
  pcuicBuild = "-I ${pcuic}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/PCUIC/";
in
mkCoqDerivation {
  pname = "cast-tests";
  owner = "MetaCoq";
  repo = "metacoq";
  defaultVersion = "8.14"; /* with versions; switch coq.coq-version [
    { case = "8.14"; out = "8.14"; }
  ] null;
*/
  src = ./cast-tests;
  outputs = ["out" "dev"];

  mlPlugin = true;
  dontInstall = true;
  dontFixup = true;

  nativeBuildInputs = [ which ];
  extraBuildInputs = [ equations pcuic template zarith ];

  preBuild = ''
    sed -i "1c ${templateBuild}" ./_CoqProject
    sed -i "2c ${pcuicBuild}" ./_CoqProject
  '';

  meta = {
    homepage = "https://github.com/MetaCoq/metacoq/";
    description = "metacoq";
    maintainers = [];
  };
}
