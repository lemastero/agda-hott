{
  description = "hott-wiki2";

  inputs = {
    nixpkgs.url = "github:ncfavier/nixpkgs/agda-updates";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in rec {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            (pkgs.agda.withPackages (ps: [ ps.standard-library ]))
          ];
        };
      }
    );
}
