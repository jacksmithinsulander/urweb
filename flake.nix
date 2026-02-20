{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = {self, nixpkgs, flake-utils} :
    flake-utils.lib.eachSystem ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"]
      (system:
        let
          pkgs = import nixpkgs { system = system; };
        in
          {
            defaultPackage = (import ./default.nix {
              pkgs = pkgs;
            });
          }
      );
}
