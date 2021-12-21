{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/21.05";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = {self, nixpkgs, flake-utils} :
    flake-utils.lib.eachDefaultSystem
      (system:
        let 
          pkgs = import nixpkgs { system = system; };
        in
          {
            defaultPackage = (import ./default.nix {
              pkgs = pkgs;
              system = system;
            });
          }
      );
}
