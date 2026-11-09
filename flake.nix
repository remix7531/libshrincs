{
  description = "libshrincs: implementation and formal verification of SHRINCS, a hybrid stateful/stateless hash-based signature scheme";

  nixConfig = {
    extra-substituters = [ "https://coq-community.cachix.org" ];
    extra-trusted-public-keys = [
      "coq-community.cachix.org-1:WBDHojv8FM6nI4ZMh43X+2g6j4WpAn+dFhjhWmLCgnA="
    ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/6dadaf4375be35033e1c84395adbd53ff5fded96";

    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-parts.inputs.nixpkgs-lib.follows = "nixpkgs";

    rocq-mcp-evolve.url = "github:remix7531/rocq-mcp-evolve/37563ebf06ca5a2d5816c72549caf44a58bd1625";

    ssprove-src = {
      url = "github:remix7531/ssprove/fdbf1c4eee2f8f760eca5abc3cefb32a2a04adf7";
      flake = false;
    };
    vst-src = {
      url = "github:remix7531/VST/8f62aee08e6cf58385422bb983426c57b3d4b0ed";
      flake = false;
    };
    rocq-src = {
      url = "github:remix7531/rocq/e90f1ee76c7119ab8c7d52dccaa0ef40ede5e6d2";
      flake = false;
    };
  };

  outputs =
    inputs@{
      flake-parts,
      nixpkgs,
      rocq-mcp-evolve,
      ssprove-src,
      vst-src,
      rocq-src,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ];

      perSystem =
        { system, ... }:
        let
          proofOcamlPackages = pkgs.ocaml-ng.ocamlPackages_5_3.overrideScope (
            ocamlFinal: _previous: {
              # Remove after the proof nixpkgs pin includes NixOS/nixpkgs#573940.
              memprof-limits = ocamlFinal.callPackage
                "${rocq-mcp-evolve.inputs.nixpkgs}/pkgs/development/ocaml-modules/memprof-limits"
                { };
            }
          );
          pkgs = import nixpkgs {
            inherit system;
            config.allowUnfreePredicate = pkg: builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
            overlays = [
              (final: prev: {
                rocqPackages_9_2 = prev.rocqPackages_9_2.overrideScope (
                  rfinal: rprev: {
                    coq = rprev.coq.override {
                      customOCamlPackages = proofOcamlPackages;
                    };
                    rocq-core = (rprev.rocq-core.override {
                      customOCamlPackages = proofOcamlPackages;
                    }).overrideAttrs (old: {
                      # Remove after upgrading to Rocq 9.4 with rocq-prover/rocq#22485 included.
                      src = rocq-src;
                    });
                    VST = rprev.VST.overrideAttrs (old: {
                      # Remove when packaged VST includes the universe and HMAC fixes.
                      src = vst-src;
                    });
                    ssprove = rprev.ssprove.overrideAttrs (old: {
                      # Remove when packaged SSProve includes the private imports and word carrier.
                      src = ssprove-src;
                    });
                  }
                );
              })
            ];
          };
          rocq = pkgs.rocqPackages_9_2;
          server = rocq-mcp-evolve.packages.${system}.default.override {
            rocq = rocq.rocq-core;
          };

          generalPackages = [
            pkgs.clang
            pkgs.gcc
            pkgs.gmp
            pkgs.gmp.dev
            pkgs.gnumake
            pkgs.m4
            pkgs.pkg-config
          ] ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [
            pkgs.valgrind
          ] ++ [
            pkgs.which
          ];

          rocqPackages = [
            rocq.coq
            server
          ];

          vstPackages = [
            rocq.VST
          ];

          ssprovePackages = [
            rocq.stdlib
            rocq.ssprove
            rocq.equations
            rocq.mathcomp-ssreflect
            rocq.mathcomp-analysis
            rocq.mathcomp-experimental-reals
            rocq.extructures
            rocq.mathcomp-word
          ];

          shellHook = "unset COQPATH";
        in
        {
          packages = {
            rocq = rocq.rocq-core;
            vst = rocq.VST;
            ssprove = rocq.ssprove;
            rocq-mcp-evolve = server;
          };
          devShells.default = pkgs.mkShell {
            inherit shellHook;
            packages = generalPackages ++ rocqPackages ++ vstPackages ++ ssprovePackages;
          };
        };
    };
}
