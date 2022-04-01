{ pkgs ? import <nixpkgs> {},
  coqPackages ? pkgs.coqPackages_8_14 }:

let
  ocamlPackages = coqPackages.coq.ocamlPackages;
  deps = {
    inherit (ocamlPackages) zarith;
    inherit (coqPackages) coq equations mkCoqDerivation;
  };
  callPackage = pkgs.lib.callPackageWith (pkgs // deps // self);
  self = {
    metacoq = {
      template = callPackage ./template-coq.nix {};
      pcuic = callPackage ./pcuic.nix {};
      #safechecker = callPackage ./safechecker.nix {};
      #erasure = callPackage ./erasure.nix {};
      #translations = callPackage ./translations.nix {};
      #test-suite = callPackage ./test-suite.nix {};
      #cast-tests = callPackage ./cast-tests.nix {};
    };
  };
in self
