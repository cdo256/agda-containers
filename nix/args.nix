{ self, inputs, ... }:
{
  systems = [
    "x86_64-linux"
  ];
  perSystem =
    { system, ... }:
    {
      _module.args = {
        pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [
            (final: prev: {
              agdaPackages = prev.agdaPackages // {
                cubical = final.agdaPackages.mkDerivation {
                  pname = "cubical";
                  version = "flake";
                  src = inputs.agda-cubical;
                };
              };
            })
          ];
        };
      };
    };
}
