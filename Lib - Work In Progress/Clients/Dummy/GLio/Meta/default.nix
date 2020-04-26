{nixpkgs ? import ./pkgs.nix {}}: nixpkgs.fstar-package-manager.build (import ./fstar-package.nix {nixpkgs = nixpkgs;})
