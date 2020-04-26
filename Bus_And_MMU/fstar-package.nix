{nixpkgs ? import <nixpkgs> {}}:
let
  lib = nixpkgs.lib;
in
{ name = "LioStar";
  sources-directory = lib.cleanSource ./.;
  force-fstar-version =
    nixpkgs.fstar-clemma-reflection-smtpat
   or (import ./pkgs.nix).fstar-clemma-reflection-smtpat      
  ;
  
  sources = [
    # "LioStar.Meta.Example"
    "LioStar.Meta"
    "LioStar.Meta.Helpers"
    
    "Core.LioStar"
    "Core.Lattice"
    "Bus.Lattice"
    "StateFull"

    "Bus.Example"
    "Bus.Lattice"    
  ];
  ocaml-sources = [];
  tactic-module = "LioStar.Meta";
  dependencies  = (with (import (
    nixpkgs.fetchFromGitHub {
      owner = "W95Psp";
      repo = "fstar-libs";
      rev = "36d2bef796a80f17d202a88a36a75e045654412b";
      sha256 = "0qygm0ksyvhxnhg658ndxpz1aji7p3i12k5gnk2795i8ppai6jva";
      fetchSubmodules = false;
    })); [
    MetaTools
  ]);
  compile       = [];
}
