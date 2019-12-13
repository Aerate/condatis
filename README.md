# condatis
Verifying Functional Reactive Programs with Side Effects
Agda >= 2.5.2 is necessary and sufficient.


# Nix support (work in progress)

`nixpkgs.callPackage (import ./default.nix { stdenv = nixpkgs.stdenv; agda = nixpkgs.agda; AgdaStdlib = nixpkgs.AgdaStdlib; }) {}`
