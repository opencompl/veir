{
  description = "VeIR Flake";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        packages = rec {
          default = veir-opt;
          veir-opt = pkgs.writeShellApplication {
            name = "veir-opt";
            runtimeInputs = [ pkgs.elan ];
            text = ''
              lake exe veir-opt "$@"
            '';
          };
        };

        apps = {
          default = flake-utils.lib.mkApp { drv = self.packages.${system}.veir-opt; };
          veir-opt = flake-utils.lib.mkApp { drv = self.packages.${system}.veir-opt; };
        };

        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.elan
            pkgs.lit
            pkgs.filecheck
          ];
         };
      });
}
