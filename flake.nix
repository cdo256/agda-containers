{
  description = "MSc Project on Virtual Sets";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs = {
      type = "github";
      owner = "nixos";
      repo = "nixpkgs";
      ref = "master";
    };
    agda-cubical = {
      type = "github";
      owner = "cdo256";
      repo = "agda-cubical";
      ref = "categories";
    };
    agda-categories = {
      type = "github";
      owner = "cdo256";
      repo = "agda-categories";
      ref = "cubical";
    };
  };

  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      debug = true;
      systems = [
        "x86_64-linux"
      ];
      imports = [
        ./nix/args.nix
        ./nix/packages.nix
        ./nix/shells.nix
      ];
    };
}
