{
  description = "libshrincs: implementation and formal verification of SHRINCS, a hybrid stateful/stateless hash-based signature scheme";

  nixConfig = {
    extra-substituters = [ "https://coq-community.cachix.org" ];
    extra-trusted-public-keys = [
      "coq-community.cachix.org-1:WBDHojv8FM6nI4ZMh43X+2g6j4WpAn+dFhjhWmLCgnA="
    ];
  };

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";

    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-parts.inputs.nixpkgs-lib.follows = "nixpkgs";

    rocq-mcp.url = "github:remix7531/rocq-mcp/develop";
    rocq-mcp.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    inputs@{
      flake-parts,
      nixpkgs,
      rocq-mcp,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      perSystem =
        { system, ... }:
        let
          pkgs = import nixpkgs {
            inherit system;
            config.allowUnfreePredicate = pkg: builtins.elem (pkgs.lib.getName pkg) [ "compcert" ];
          };
          rocq = pkgs.coqPackages_9_0;

          generalPackages = [
            pkgs.clang
            pkgs.gcc
            pkgs.gmp
            pkgs.gmp.dev
            pkgs.gnumake
            pkgs.m4
            pkgs.pkg-config
            pkgs.valgrind
            pkgs.which
          ];

          rocqPackages = [
            rocq.coq
            rocq.coq-lsp
            rocq.vsrocq-language-server
            rocq-mcp.packages.${system}.rocq-mcp
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
          ];

          shellHook = "unset COQPATH";
        in
        {
          devShells.c = pkgs.mkShell {
            packages = generalPackages;
          };
          devShells.vst = pkgs.mkShell {
            inherit shellHook;
            packages = generalPackages ++ rocqPackages ++ vstPackages;
          };
          devShells.ssprove = pkgs.mkShell {
            inherit shellHook;
            packages = generalPackages ++ rocqPackages ++ ssprovePackages;
          };
          devShells.default = pkgs.mkShell {
            inherit shellHook;
            packages = generalPackages ++ rocqPackages ++ vstPackages ++ ssprovePackages;
          };
        };
    };
}
