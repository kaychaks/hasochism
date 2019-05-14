    { nixpkgs ? import <nixpkgs> {}, compiler ? "ghc864"}:
    let
    inherit (nixpkgs) pkgs;
    haskellPackages = pkgs.haskell.packages.${compiler};
    in
        {
            hasochism = haskellPackages.developPackage {
                returnShellEnv = false;
                root = ./.;
            };
        }
