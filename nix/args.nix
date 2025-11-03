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
                  buildInputs = [
                    prev.ghc
                    prev.agda
                  ];
                  buildPhase = ''
                    cp -r $src $TMPDIR/src
                    chmod -R +w $TMPDIR/src
                    cd $TMPDIR/src
                    runhaskell Everythings.hs gen-except Codata Papers
                    agda Cubical/README.agda
                  '';
                  installPhase = ''
                    cp -r $TMPDIR/src $out
                  '';
                });
                agda-categories = prev.agdaPackages.agda-categories.overrideAttrs (old: {
                  version = "9.0.0";
                  src = inputs.agda-categories;
                  sha256 = "";
                  buildPhase = ''
                    cp -r $src $TMPDIR/src
                    chmod -R +w $TMPDIR/src
                    cd $TMPDIR/src
                    agda --build-library
                  '';
                  installPhase = ''
                    cp -r $TMPDIR/src $out
                  '';
                });
              };
            })
          ];
        };
      };
    };
}
