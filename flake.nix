{
  description = "Verified Intermediate Representation";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

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

      # Lean's prebuilt macOS libraries require macOS 15.
      developmentEnvironment = pkgs: nixpkgs.lib.optionalAttrs pkgs.stdenv.hostPlatform.isDarwin {
        MACOSX_DEPLOYMENT_TARGET = "15.0";
      };

      developmentPackages = pkgs: with pkgs; [
        bash
        typst
        claude-code
        (llvmPackages pkgs).clang
        elan
        gmp
        gnumake
        (llvmPackages pkgs).llvm
        (llvmPackages pkgs).mlir
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
            runtimeEnv = developmentEnvironment pkgs;
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

      makeLeanApp = pkgs: target:
        let
          package = pkgs.writeShellApplication {
            name = target;
            runtimeInputs = developmentPackages pkgs;
            runtimeEnv = developmentEnvironment pkgs;
            text = ''
              export LEAN_AR="${(llvmPackages pkgs).llvm}/bin/llvm-ar"
              export LEAN_CC="${self}/ExArray/compiler"
              exec lake exe ${target} "$@"
            '';
          };
        in
        {
          type = "app";
          program = "${package}/bin/${target}";
          meta.description = "Run VeIR's ${target} executable";
        };
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = pkgs.mkShell ({
            packages = developmentPackages pkgs;
            buildInputs = nixpkgs.lib.optionals pkgs.stdenv.hostPlatform.isDarwin [
              (pkgs.darwinMinVersionHook "15.0")
            ];

            # The clang wrapper's default hardening defines `_FORTIFY_SOURCE`,
            # and glibc warns about it at `-O0`, which `lake build --iofail`
            # turns into a failure of every C file of a debug build.
            hardeningDisable = [ "fortify" "fortify3" ];

            # ExArray uses Clang LTO and therefore needs its compiler wrapper
            # together with LLVM's archiver.
            LEAN_AR = "${(llvmPackages pkgs).llvm}/bin/llvm-ar";
            LEAN_CC = "${self}/ExArray/compiler";
          } // developmentEnvironment pkgs);
        });

      apps = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
        in
        {
          default = makeApp pkgs null;
          build = makeApp pkgs "build";
          tests = makeApp pkgs "tests";
          "veir-opt" = makeLeanApp pkgs "veir-opt";
          "veir-interpret" = makeLeanApp pkgs "veir-interpret";
          "veir2mir" = makeLeanApp pkgs "veir2mir";
          "run-benchmarks" = makeLeanApp pkgs "run-benchmarks";
        });
    };
}
