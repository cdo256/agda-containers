# Builder for local Agda packages.
# Ported from nixpkgs agda.withPackages'
{
  stdenv,
  lib,
  Agda,
  writeShellScriptBin,
  nixosTests,
}:

let
  pname = "${Agda.meta.mainProgram}Local";
  version = Agda.version;

  agdaBin = writeShellScriptBin "${Agda.meta.mainProgram}" ''
    exec ${lib.getExe Agda} --library-file="''${DIRENV_DIR:1}/local-libraries" "$@"
  '';

  agdaModeBin = writeShellScriptBin "agda-mode" ''
    exec ${lib.getExe' Agda "agda-mode"} "$@"
  '';

in
stdenv.mkDerivation {
  inherit pname version;
  passthru = {
    unwrapped = Agda;
    tests = {
      inherit (nixosTests) agda;
    };
  };
  phases = [ "installPhase" ];
  installPhase = ''
    mkdir -p $out/bin
    cp ${agdaBin}/bin/${Agda.meta.mainProgram} $out/bin/${Agda.meta.mainProgram}
    cp ${agdaModeBin}/bin/agda-mode $out/bin/agda-mode
  '';
  meta = removeAttrs Agda.meta [ "outputsToInstall" ];
}
