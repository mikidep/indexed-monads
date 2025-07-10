{
  description = "An empty flake template that you can adapt to your own environment";
  inputs = {
    # Flake inputs
    nixpkgs.url = "nixpkgs/nixos-unstable";
    cubical-containers = {
      url = "github:phijor/cubical-containers?ref=90eab18";
      flake = false;
    };
    cubical-categorical-logic = {
      url = "github:maxsnew/cubical-categorical-logic?ref=feaab16";
      flake = false;
    };
    # agda-index = {
    #   url = "github:phijor/agda-index";
    #   inputs.nixpkgs.follows = "nixpkgs";
    # };
  };

  # Flake outputs
  outputs = inputs @ {
    self,
    nixpkgs,
    # agda-cubical,
    # agda-index,
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
          };
        });
  in {
    packages = forEachSupportedSystem ({
      pkgs,
      system,
    }: let
      cubical = pkgs.agdaPackages.cubical;
      cubical-categorical-logic = pkgs.agdaPackages.mkDerivation {
        pname = "cubical-categorical-logic";
        version = "feaab16";
        src = inputs.cubical-categorical-logic;
        preConfigure = ''
          make Everything.agda
        '';
        buildInputs = [cubical];
        meta = {
          description = "Extensions to the cubical stdlib category theory for categorical logic/type theory";
          platforms = pkgs.lib.platforms.all;
        };
      };
      cubical-containers = pkgs.agdaPackages.mkDerivation {
        pname = "cubical-containers";
        version = "90eab18";
        src = inputs.cubical-containers;
        postPatch = ''
          patchShebangs ./gen-everything.sh
        '';
        buildPhase = ''
          runHook preInstall

          echo 'Generating list of modules...'
          ./gen-everything.sh

          echo 'Checking `Everything.agda`...'
          agda ./Everything.agda

          echo 'Checking `README.agda`...'
          agda ./README.agda

          echo "Generating HTML docs..."
          agda --html --html-dir=$html --highlight-occurrences ./README.agda

          runHook postInstall
        '';
        buildInputs = [cubical cubical-categorical-logic];
        meta = {
          platforms = pkgs.lib.platforms.all;
        };
      };
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
        # cubical-categorical-logic
        # cubical-containers
      ];
      docs = pkgs.stdenv.mkDerivation {
        name = "indexed-monads-docs";
        pname = "indexed-monads-docs";
        buildInputs = [agdaWithLibs];
        src = ./.;
        buildPhase = ''
          runHook preBuild
          mkdir $out
          agda --html --html-dir=$out src/index.agda
          runHook postBuild
        '';
      };
      default = indexed-monads;
      # agda-search = pkgs.writeShellApplication {
      #   name = "agda-search";
      #   runtimeInputs = with pkgs; [fzf firefox (agda-index.packages.${system}.default)];
      #   text = ''
      #     agda-index ${docs}/ | fzf -d' ' --with-nth='2' | cut -d' ' -f1 | xargs -I % firefox --new-window %
      #   '';
      # };
    });
  };
}
