{
  perSystem =
    { self', pkgs, ... }:
    {
      devShells = rec {
        local-libraries = pkgs.mkShell {
          buildInputs = with self'.packages; [
            agda-local
            just-agda-local
            #pkgs.haskellPackages.agda-language-server
            (pkgs.python312.withPackages (p: [
              p.matplotlib
            ]))
            pkgs.texlab
            pkgs.ltex-ls
            pkgs.pandoc
            tex
            pkgs.fira-mono
            pkgs.dejavu_fonts
            pkgs.fontconfig
            pkgs.julia-mono
          ];
          shellHook = ''
            fc-cache -f
          '';
        };
        flake-libraries = pkgs.mkShell {
          buildInputs = with self'.packages; [
            agda
            just-agda
            #pkgs.haskellPackages.agda-language-server
            (pkgs.python312.withPackages (p: [
              p.matplotlib
            ]))
            pkgs.texlab
            pkgs.ltex-ls
            pkgs.pandoc
            tex
            pkgs.fira-mono
            pkgs.dejavu_fonts
            pkgs.fontconfig
            pkgs.julia-mono
          ];
          shellHook = ''
            fc-cache -f
          '';
        };
        default = local-libraries;
      };
    };
}
