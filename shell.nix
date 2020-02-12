let
  pkgs = import (builtins.fetchTarball {
        name = "nixos-unstable";
        url = https://github.com/NixOS/nixpkgs/archive/6670b4c37d4acfd4c2149fd60356d2d88c3ae4ef.tar.gz;
        # Hash obtained using `nix-prefetch-url --unpack <url>`
        sha256 = "11xjg3h1k3v9x7qryvfrgcxc0ysxkhfbfiyiqdld2rf5rns6hsxz";
      }) {};
      polyml = pkgs.callPackage ./nix/polyml {};
      isabelle = pkgs.callPackage ./nix/isabelle { polyml = polyml; java = pkgs.openjdk11; nettools = pkgs.nettools; z3 = pkgs.z3; };
in
  pkgs.stdenv.mkDerivation {
    name = "isabelle-prover-cookbook";
    buildInputs = [ isabelle ];
    shellHook = ''
    '';
  }
