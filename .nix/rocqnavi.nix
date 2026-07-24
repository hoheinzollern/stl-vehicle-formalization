# rocqnavi (affeldt-aist/rocqnavi), a coq2html fork used to generate the
# HTML documentation. Not yet in nixpkgs, so we build it from a pinned
# source. Build:  nix-build .nix/rocqnavi.nix  ->  result/bin/rocqnavi
{ pkgs ? import <nixpkgs> { } }:

pkgs.stdenv.mkDerivation {
  pname = "rocqnavi";
  version = "unstable-2026-07-24";

  src = pkgs.fetchFromGitHub {
    owner = "affeldt-aist";
    repo = "rocqnavi";
    rev = "378ad6c9959a151e1380e548e61b61698ee1c023";
    hash = "sha256-QfEP4qBbP0FLoxnjLe26tmZCpMg7Xu/gk6OXxL6Fdc4=";
  };

  nativeBuildInputs = [ pkgs.ocaml pkgs.ocamlPackages.findlib ];
  buildInputs = [ pkgs.ocamlPackages.dune-glob pkgs.ocamlPackages.yojson ];

  installPhase = ''
    runHook preInstall
    make PREFIX=$out install
    runHook postInstall
  '';

  meta = {
    description = "rocqnavi: coq2html-fork HTML documentation generator for Rocq";
    homepage = "https://github.com/affeldt-aist/rocqnavi";
    license = pkgs.lib.licenses.gpl2Plus;
  };
}
