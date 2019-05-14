    { nixpkgs ? import <nixpkgs> {}, compiler ? "ghc864", withHoogle ? false}:
    let
    inherit (nixpkgs) pkgs;
    haskellPackages = pkgs.haskell.packages.${compiler};
    project = import ./. { inherit nixpkgs compiler; };
    in
    with haskellPackages;
    shellFor {
      inherit withHoogle;
      packages = p: [ project.hasochism ];
      buildInputs = [
        ghcid
        cabal-install
        hlint
        hoogle
        fast-tags
        pointfree
        hindent
        stylish-haskell
      ];
    }
