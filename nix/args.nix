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
                cubical = prev.agdaPackages.cubical.overrideAttrs (old: {
                  version = "9.0.0";
                  src = inputs.agda-cubical;
                  sha256 = "";
                  buildPhase = ''
                    echo foo
                  '';
                });
                agda-categories = prev.agdaPackages.agda-categories.overrideAttrs (old: {
                  version = "9.0.0";
                  src = inputs.agda-categories;
                  sha256 = "";
                });
              };
            })
          ];
        };
      };
    };
}
