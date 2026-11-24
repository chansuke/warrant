{
  description = "Warrant: a verified, parallel language for AI agents";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.rust-overlay = {
    url = "github:oxalica/rust-overlay";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    { nixpkgs, rust-overlay, ... }:
    let
      # perf and the z3 release binary are Linux only, like CI.
      systems = [ "x86_64-linux" ];
      forAllSystems =
        f:
        nixpkgs.lib.genAttrs systems (
          system:
          f (
            import nixpkgs {
              inherit system;
              overlays = [ rust-overlay.overlays.default ];
            }
          )
        );
      # The release CI installs (Z3_VERSION and Z3_SHA256 in ci.yml). nixpkgs
      # moves to newer z3, and proofs and timeouts change between releases.
      z3 =
        pkgs:
        pkgs.stdenv.mkDerivation rec {
          pname = "z3";
          version = "5.1.0";
          src = pkgs.fetchurl {
            url = "https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-2.39.zip";
            sha256 = "f47be8d27d3230e823bf1eeede2fe0abaca55bb78d0b59974370e6689a92284a";
          };
          nativeBuildInputs = [
            pkgs.unzip
            pkgs.autoPatchelfHook
          ];
          buildInputs = [ pkgs.stdenv.cc.cc.lib ];
          installPhase = ''
            install -Dm755 bin/z3 $out/bin/z3
          '';
        };
    in
    {
      formatter = forAllSystems (pkgs: pkgs.nixfmt);

      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
            (z3 pkgs)
            # formal/tla/check.sh runs TLC on a JVM; formal/lean/check.sh
            # needs elan to fetch the toolchain in formal/lean/lean-toolchain.
            pkgs.jdk21_headless
            pkgs.elan
            # scripts/flamegraph.sh and scripts/profile-breakdown.sh.
            pkgs.perf
            pkgs.inferno
          ];
        };
      });
    };
}
