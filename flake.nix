{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    qik.url         = "github:indypaige/qik";
  };

  outputs        = { flake-utils, qik, ... }:
    flake-utils.lib.eachDefaultSystem (system: {
      packages.default = qik.lib.${system}.haskell.mk {
        name = "lam";
        root = ./.;
      };
    });
}
