{
  description = "Verified Intermediate Representation";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs = { self, nixpkgs, ... }:
    let
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
      llvmPackages = pkgs: pkgs.llvmPackages_23;

      developmentPackages = pkgs: with pkgs; [
        bash
        clang
        elan
        gmp
        gnumake
        (llvmPackages pkgs).llvm
        ((llvmPackages pkgs).mlir.overrideAttrs (oldAttrs: {
          # Nixpkgs does not enable MLIR's test dialect. VeIR's PDL tests
          # use that dialect when checking compatibility with mlir-opt.
          cmakeFlags = oldAttrs.cmakeFlags ++ [
            (lib.cmakeBool "MLIR_INCLUDE_TESTS" true)
          ];
        }))
        pkg-config
        uv
      ];

      makeApp = pkgs: target:
        let
          suffix = if target == null then "help" else target;
          command = if target == null then "make" else "make ${target}";
          package = pkgs.writeShellApplication {
            name = "veir-${suffix}";
            runtimeInputs = developmentPackages pkgs;
            text = ''
              export LEAN_AR="${(llvmPackages pkgs).llvm}/bin/llvm-ar"
              export LEAN_CC="${self}/ExArray/compiler"
              exec ${command} "$@"
            '';
          };
        in
        {
          type = "app";
          program = "${package}/bin/veir-${suffix}";
          meta.description =
            if target == null
            then "Show VeIR's Make targets"
            else "Run VeIR's make ${target} target";
        };
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell {
            packages = developmentPackages pkgs;

            # ExArray uses Clang LTO and therefore needs its compiler wrapper
            # together with LLVM's archiver.
            LEAN_AR = "${(llvmPackages pkgs).llvm}/bin/llvm-ar";
            LEAN_CC = "${self}/ExArray/compiler";
          };
        });

      apps = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = makeApp pkgs null;
          build = makeApp pkgs "build";
          tests = makeApp pkgs "tests";
        });
    };
}
