{
  inputs = {
    naersk.url = "github:nix-community/naersk/master";
    nixpkgs.url = "https://channels.nixos.org/nixpkgs-unstable/nixexprs.tar.zst";
    utils.url = "github:numtide/flake-utils";
    # Upstream CaDiCaL, pinned to the same commit as the ./cadical checkout.
    cadical-src = {
      url = "github:arminbiere/cadical/c60730422e758ef1cebe7aeddf2dda31c996bf04";
      flake = false;
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      utils,
      naersk,
      cadical-src,
    }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        naersk-lib = pkgs.callPackage naersk { };

        # Reference C++ CaDiCaL built from the vendored sources in ./cadical.
        # Used for head-to-head comparisons against the Rust port.
        cadical-ref = pkgs.stdenv.mkDerivation {
          pname = "cadical-ref";
          version = pkgs.lib.strings.trim (builtins.readFile "${cadical-src}/VERSION");
          src = cadical-src;
          nativeBuildInputs = [ pkgs.gnumake ];
          configurePhase = ''
            patchShebangs configure scripts
            ./configure
          '';
          buildPhase = "make -C build -j$NIX_BUILD_CORES";
          installPhase = ''
            mkdir -p $out/bin $out/lib $out/include
            cp build/cadical build/mobical $out/bin/
            cp build/libcadical.a $out/lib/
            cp src/cadical.hpp src/ccadical.h src/ipasir.h $out/include/
          '';
        };

        # Proof and model checkers used by CaDiCaL's regression suite.
        cadical-checkers = pkgs.stdenv.mkDerivation {
          pname = "cadical-checkers";
          version = "1";
          src = "${cadical-src}/test/cnf";
          buildInputs = [ pkgs.zlib ];
          buildPhase = ''
            printf '#define VERSION "cadical-test"\n#define COMPILE "cc -O"\n' > config.h
            cc -O -I. -o dimocheck dimocheck.c -lz
            cc -O -o drat-trim drat-trim.c
            cc -O -o lrat-trim lrat-trim.c
          '';
          installPhase = ''
            mkdir -p $out/bin
            cp dimocheck drat-trim lrat-trim $out/bin/
          '';
        };

        cadical-rs = naersk-lib.buildPackage ./.;
      in
      {
        packages = {
          default = cadical-rs;
          inherit cadical-rs cadical-ref cadical-checkers;
        };
        defaultPackage = cadical-rs;
        devShell =
          with pkgs;
          mkShell {
            buildInputs = [
              cargo
              rustc
              rustfmt
              pre-commit
              rustPackages.clippy
              gnumake
              zlib
              xz
              gzip
              bzip2
              cadical-ref
              cadical-checkers
            ];
            RUST_SRC_PATH = rustPlatform.rustLibSrc;
            CADICAL_REF = "${cadical-ref}";
          };
      }
    );
}
