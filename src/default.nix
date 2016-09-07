# to build using nix:
#
# install nix from nix website
#
# type: nix-shell --pure
#
# type: make

# http://hydra.nixos.org/build/25162838/download/1/nixpkgs/manual.html#users-guide-to-the-haskell-infrastructure
{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghc7101" }:
let
  inherit (nixpkgs) pkgs;
  coq = import ./.nix/coq {
    inherit (pkgs)  stdenv fetchgit writeText pkgconfig ncurses;
    inherit (pkgs.ocamlPackages_4_01_0) ocaml findlib lablgtk;
    camlp5 = pkgs.ocamlPackages_4_01_0.camlp5_transitional;
  };
  ghc = pkgs.haskell.packages.${compiler}.ghcWithPackages (ps: with ps; [
    HFuse
  ]);
in
pkgs.stdenv.mkDerivation {
  name = "my-haskell-env-0";
  buildInputs = [ ghc coq pkgs.python ];
  shellHook = "eval $(egrep ^export ${ghc}/bin/ghc)";
}
