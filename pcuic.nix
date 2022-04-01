{ lib, mkCoqDerivation, version ? null
, equations, metacoq, which, zarith }:

mkCoqDerivation {
  pname = "pcuic";
  owner = "MetaCoq";
  repo = "metacoq";
  inherit version;
  defaultVersion = "8.14"; /* with versions; switch coq.coq-version [
    { case = "8.14"; out = "8.14"; }
  ] null;
*/

  src = ./pcuic;

  mlPlugin = true;

  nativeBuildInputs = [ which ];
  extraBuildInputs = [ equations metacoq.template zarith ];

  preBuild = ''
    touch metacoq-config
    patchShebangs clean_extraction.sh
    patchShebangs theories/replace.sh
  '';

  meta = {
    homepage = "https://github.com/MetaCoq/metacoq/";
    description = "metacoq";
    maintainers = [];
  };
}
