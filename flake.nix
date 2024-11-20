{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    miking.url = "github:elegios/miking/new-build-system?dir=misc/packaging";
  };

  outputs = { self, nixpkgs, miking }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux.pkgs;
      shell = pkgs.mkShell {
        name = "TreePPL dev shell";
        buildInputs = [
          miking.packages.x86_64-linux.default
          nixpkgs.legacyPackages.x86_64-linux.ocamlPackages.owl
          nixpkgs.legacyPackages.x86_64-linux.gdb
          nixpkgs.legacyPackages.x86_64-linux.tup
        ];
      };
    in {
      # package.x86_64-linux.default = miking;
      devShells.x86_64-linux.default = shell;
    };
}
