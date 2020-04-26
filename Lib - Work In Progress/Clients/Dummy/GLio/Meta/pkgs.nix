{nixpkgs ? import <nixpkgs> {}}:
let
  self = nixpkgs // (
    (import /etc/nixos/overlays/fstar)
    # import (nixpkgs.fetchFromGitHub {
    #   owner = "W95Psp";
    #   repo = "fstar-nix-packer";
    #   rev = "3120698470ce23ab2052a465f107c35ccd5ea595";
    #   sha256 = "18d2pajilv7gbbxg15b8mcgw09wgamn2qdn8z0gi2wnqyqf4x016";
    # })
      self
      nixpkgs
  );
in
self
      
