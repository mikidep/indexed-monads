{
  description = "An empty flake template that you can adapt to your own environment";
  inputs = {
    # Flake inputs
    nixpkgs.url = "nixpkgs/nixos-unstable";
    agda-cubical = {
      url = "github:agda/cubical/2f085f5";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    agda-index = {
      url = "github:phijor/agda-index";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # Flake outputs
  outputs = {
    self,
    nixpkgs,
    agda-cubical,
    agda-index,
    ...
  }: let
    # The systems supported for this flake
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
          inherit system;
          pkgs = import nixpkgs {
            inherit system;
            overlays = [agda-cubical.overlays.default];
          };
        });
  in {
    devShells = forEachSupportedSystem ({
      system,
      pkgs,
    }: {
      default = pkgs.mkShell {
        # The Nix packages provided in the environment
        # Add any you need here
        packages = [self.packages.${system}.agdaWithCubical self.packages.${system}.agda-search];

        # Set any environment variables for your dev shell
        env = {};

        # Add any shell logic you want executed any time the environment is activated
        shellHook = ''
        '';
      };
    });
    packages = forEachSupportedSystem ({pkgs, ...}: rec {
      agdaWithCubical = pkgs.agda.withPackages (_: [pkgs.cubical]);
      docs = pkgs.stdenv.mkDerivation {
        name = "indexed-monads-docs";
        pname = "indexed-monads-docs";
        buildInputs = [agdaWithCubical];
        src = ./.;
        buildPhase = ''
          runHook preBuild
          mkdir $out
          agda --html --html-dir=$out index.agda
          runHook postBuild
        '';
      };
      agda-search = pkgs.writeShellApplication {
        name = "agda-search";
        runtimeInputs = with pkgs; [fzf firefox (agda-index.packages.${system}.default)];
        text = ''
          agda-index ${docs}/ | fzf -d' ' --with-nth='2' | cut -d' ' -f1 | xargs -I % firefox --new-window %
        '';
      };
    });
  };
}
