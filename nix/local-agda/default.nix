# Builder for local Agda packages.
# Ported from nixpkgs agda.withPackages'
{
  stdenv,
  lib,
  Agda,
  runCommand,
  makeWrapper,
  writeText,
  nixosTests,
}:
let
  pname = "${Agda.meta.mainProgram}Local";
  version = Agda.version;
in
runCommand "${pname}-${version}"
  {
    inherit pname version;
    nativeBuildInputs = [ makeWrapper ];
    passthru = {
      unwrapped = Agda;
      tests = {
        inherit (nixosTests) agda;
      };
    };
    # Agda is a split package with multiple outputs; do not inherit them here.
    meta = removeAttrs Agda.meta [ "outputsToInstall" ];
  }
  ''
    mkdir -p $out/bin
    makeWrapper ${lib.getExe Agda} $out/bin/${Agda.meta.mainProgram} \
      --add-flags "--library-file=./local-libraries"
    if [ -e ${lib.getExe' Agda "agda-mode"} ]; then
      ln -s ${lib.getExe' Agda "agda-mode"} $out/bin/agda-mode
    fi
  ''
