{ lib, mkCoqDerivation, version ? null
, coq, metacoq, equations, which, zarith }:

with metacoq;
let
  templateBuild = "-I ${template}/lib/coq/${coq.coq-version}/user-contrib/MetaCoq/Template/";
in
mkCoqDerivation {
  pname = "safechecker";
  owner = "MetaCoq";
  repo = "metacoq";
  inherit version;
  defaultVersion = "8.14"; /* with versions; switch coq.coq-version [
    { case = "8.14"; out = "8.14"; }
  ] null;
*/

  src = ./safechecker;

  mlPlugin = true;

  nativeBuildInputs = [ which ];
  extraBuildInputs = [ equations pcuic template zarith ];

  preBuild = ''
    echo "${templateBuild}" >> metacoq-config
    patchShebangs clean_extraction.sh
  '';

  meta = {
    homepage = "https://github.com/MetaCoq/metacoq/";
    description = "metacoq";
    maintainers = [];
  };
}
