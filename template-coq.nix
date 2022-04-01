{ lib, mkCoqDerivation, version ? null
, coq, equations, which, zarith }:

with lib; mkCoqDerivation {
  pname = "template-coq";
  owner = "MetaCoq";
  repo = "metacoq";
  inherit version;
  defaultVersion = "8.14"; /* with versions; switch coq.coq-version [
    { case = "8.14"; out = "8.14"; }
  ] null;
*/
 
  src = ./template-coq;

  mlPlugin = true;

  nativeBuildInputs = [ which ];
  extraBuildInputs = [ equations zarith ];

  preBuild = ''
    patchShebangs update_plugin.sh
  '';

  meta = {
    homepage = "https://github.com/MetaCoq/metacoq/";
    description = "metacoq";
    maintainers = [];
  };
}
