{ inputs, ... }:
{
  perSystem =
    { system, pkgs, ... }:
    {
      config.packages = rec {
        agda-base = pkgs.agda;
        agda-local = pkgs.callPackage ./local-agda { inherit (pkgs.haskellPackages) Agda; };
        agda-cubical = pkgs.agdaPackages.cubical;
        agda-categories = pkgs.agdaPackages.agda-categories;
        agda = agda-base.withPackages (ps: [
          ps.standard-library
          pkgs.agdaPackages.cubical
          pkgs.agdaPackages.agda-categories
        ]);
        tex = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-medium
            latexmk
            standalone
            pgf
            amsmath
            biblatex
            tikz-cd
            latex-bin
            minted
            #ifxetex
            #ifluatex
            xifthen
            xcolor
            polytable
            etoolbox
            environ
            #xparse
            xkeyval
            ifmtarg
            lazylist
            newunicodechar
            catchfilebetweentags
            titling
            dirtree
            ;
        };
      };
    };
}
