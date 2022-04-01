{ lib, mkCoqDerivation, version ? null
, coq, equations, metacoq, which, zarith }:

with metacoq;
let
  templateBuild = "-I ${template}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/Template/";
  pcuicBuild = "-I ${pcuic}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/PCUIC/";
  safecheckerBuild = "-I ${safechecker}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/SafeChecker/";
  #erasureBuild = "-I ${erasure}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/Erasure/";
in
mkCoqDerivation {
  pname = "test-suite";
  owner = "MetaCoq";
  repo = "metacoq";
  inherit version;
  defaultVersion = "8.14"; /* with versions; switch coq.coq-version [
    { case = "8.14"; out = "8.14"; }
  ] null;
*/
  src = ./cast-tests;

  mlPlugin = true;
  dontInstall = true;
  dontFixup = true;

  nativeBuildInputs = [ which ];
  extraBuildInputs = [ equations pcuic safechecker template zarith ];

  preBuild = ''
    sed -i "1c ${templateBuild}" ./_CoqProject
    sed -i "2c ${pcuicBuild}" ./_CoqProject
    sed -i "3c ${safecheckerBuild}" ./_CoqProject
    sed -i "4c ${erasureBuild}" ./_CoqProject
    sed -i "5,7d" ./_CoqProject
    sed -i "1c ${templateBuild}" ./plugin-demo/_CoqProject
    sed -i "2d" ./plugin-demo/_CoqProject
    sed -i "1c ${templateBuild}" ./plugin-demo/_PluginProject
    sed -i "2d" ./plugin-demo/_PluginProject
    sed -i "1c From MetaCoq.Template Require Import Extraction." ./plugin-demo/theories/Extraction.v
  '';

  meta = {
    homepage = "https://github.com/MetaCoq/metacoq/";
    description = "metacoq";
    maintainers = [];
  };
}
