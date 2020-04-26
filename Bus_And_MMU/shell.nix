{nixpkgs ? import ./pkgs.nix {}}: nixpkgs.fstar-package-manager.shell (import ./fstar-package.nix {nixpkgs = nixpkgs;})
