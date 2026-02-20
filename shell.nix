let
  pkgs = import <nixpkgs> {};
  urweb = import ./default.nix { pkgs = pkgs; };
in
pkgs.mkShell {
  buildInputs = [
    pkgs.mlton
    pkgs.libmysqlclient
    pkgs.postgresql
    pkgs.sqlite
    pkgs.libunistring
    pkgs.samurai
    pkgs.gcc
    pkgs.smlnj
  ];
}
