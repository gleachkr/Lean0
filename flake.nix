{
  description = "Lean0: certifying Lean 4 environments with Metamath Zero";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    mm0.url = "github:gleachkr/mm0";
    # mm0-zig and abc (Aufbau's proof assistant, for the hand proofs in spec/)
    aufbau.url = "github:gleachkr/Aufbau/v0.0.19";
    aufbau.inputs.mm0.follows = "mm0";
  };

  outputs = { self, nixpkgs, mm0, aufbau }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system} system);
      # mm0-c has fixed capacities that large certificates overflow:
      # - the spec's term and theorem names, in tries of 2^16 and 2^20 nodes (all of Init:
      #   "trie overflow");
      # - a 64 MB expression store (one Std statement, a tree as text: "store overflow");
      # - a 512 MB input buffer for the `.mm0` text (Std's later parts, which restate the
      #   earlier ones: "Input buffer overflow");
      # - a 256-entry unify stack (a deeply nested Std statement: "unify stack overflow").
      # Capacity only: every access is bounds-checked, and store offsets are u32 (tagged in
      # their low 2 bits). Past 2 GB of static arrays, the medium code model is needed to link.
      mm0-c = system: mm0.packages.${system}.mm0-c.overrideAttrs (o: {
        postPatch = (o.postPatch or "") + ''
          sed -i -e 's/^#define THM_TRIE_SIZE (1 << 20)$/#define THM_TRIE_SIZE (1 << 22)/' \
                 -e 's/^#define TERM_TRIE_SIZE (1 << 16)$/#define TERM_TRIE_SIZE (1 << 22)/' \
                 -e 's/^#define STORE_SIZE (1 << 26)$/#define STORE_SIZE (1 << 29)/' \
                 -e 's/^#define INPUT_SIZE (1 << 29)$/#define INPUT_SIZE ((size_t)1 << 31)/' \
                 -e 's/^#define UNIFY_STACK_SIZE 256$/#define UNIFY_STACK_SIZE 65536/' \
            mm0-c/verifier_types.c
          grep -q '^#define THM_TRIE_SIZE (1 << 22)$' mm0-c/verifier_types.c
          grep -q '^#define TERM_TRIE_SIZE (1 << 22)$' mm0-c/verifier_types.c
          grep -q '^#define STORE_SIZE (1 << 29)$' mm0-c/verifier_types.c
          grep -q '^#define INPUT_SIZE ((size_t)1 << 31)$' mm0-c/verifier_types.c
          grep -q '^#define UNIFY_STACK_SIZE 65536$' mm0-c/verifier_types.c
          sed -i 's/^gcc main.c -O2/gcc main.c -mcmodel=medium -O2/' mm0-c/make.sh
          [ "$(grep -c -- '-mcmodel=medium' mm0-c/make.sh)" = 2 ]
        '';
      });
      # nanoda_lib at the commit scripts/nanoda.sh pins (keep REV in step), with Lean0's patch
      nanoda = pkgs: pkgs.applyPatches {
        name = "nanoda_lib-lean0";
        src = pkgs.fetchFromGitHub {
          owner = "ammkrn";
          repo = "nanoda_lib";
          rev = "d0a02cc5defadd683f62f9d078f41688314fa31f";
          hash = "sha256-fEK335/tJ2lEKsQVWWCLfpB+qZ23oEwv9ZQBzxRMOts=";
        };
        patches = [ ./patches/nanoda_lib.patch ];
      };
      # lean0, the one binary (generator, statement checker, the text to verify against)
      lean0' = pkgs: pkgs.rustPlatform.buildRustPackage {
        pname = "lean0";
        version = "0.1.0";
        src = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./Cargo.toml ./Cargo.lock ./lean0 ./lean0-check ./mm0kit ./spec/lean.mm0
            # the TG library's statements, embedded by lean0-check (TG mode)
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "mm0") ./spec/tg)
          ];
        };
        # the crates' path dependency on build/nanoda
        postUnpack = ''
          mkdir -p $sourceRoot/build
          cp -r ${nanoda pkgs} $sourceRoot/build/nanoda
          chmod -R u+w $sourceRoot/build/nanoda
        '';
        cargoLock.lockFile = ./Cargo.lock;
        cargoBuildFlags = [ "-p" "lean0" ];
        # scripts/test.sh is the test suite (it needs Lean and the verifiers)
        doCheck = false;
        meta.mainProgram = "lean0";
      };
    in {
      packages = forAll (pkgs: system: {
        lean0 = lean0' pkgs;
        default = lean0' pkgs;
        mm0-c = mm0-c system;
        mm0-zig = aufbau.packages.${system}.default;
        inherit (mm0.packages.${system}) mm0-rs;
      });

      devShells = forAll (pkgs: system: {
        default = pkgs.mkShell {
          packages = [
            pkgs.cargo pkgs.rustc pkgs.rustfmt pkgs.clippy
            pkgs.elan
            pkgs.perf
            (mm0-c system)
            aufbau.packages.${system}.default
            mm0.packages.${system}.mm0-rs
          ];
        };
      });
    };
}
