{
  description = "A Nix flake for the indexed-monads Agda project";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
  };

  outputs = inputs @ {nixpkgs, ...}: let
    supportedSystems = [
      "x86_64-linux" # 64-bit Intel/AMD Linux
      "aarch64-linux" # 64-bit ARM Linux
      "x86_64-darwin" # 64-bit Intel macOS
      "aarch64-darwin" # 64-bit ARM macOS
    ];

    # Helper to provide system-specific attributes
    forEachSupportedSystem = f:
      nixpkgs.lib.genAttrs supportedSystems (system:
        f {
          pkgs = import nixpkgs {
            inherit system;
          };
        });
  in {
    packages = forEachSupportedSystem ({pkgs}: let
      cubical = pkgs.agdaPackages.cubical;
      indexed-monads = pkgs.agdaPackages.mkDerivation {
        pname = "indexed-monads";
        version = "0.1";
        src = ./.;
        everythingFile = "src/Everything.agda";
        buildInputs = [cubical];
        meta = {
          platforms = pkgs.lib.platforms.all;
        };
      };
    in rec {
      agdaWithLibs = pkgs.agda.withPackages [
        cubical
      ];
      docs = pkgs.stdenv.mkDerivation {
        name = "indexed-monads-docs";
        pname = "indexed-monads-docs";
        buildInputs = [agdaWithLibs];
        src = ./.;
        buildPhase = ''
          runHook preBuild
          mkdir $out
          agda --html --html-dir=$out src/Everything.agda
          runHook postBuild
        '';
      };
      default = indexed-monads;
    });
  };
}
