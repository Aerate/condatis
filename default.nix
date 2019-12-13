{ stdenv, agda, AgdaStdlib }:

agda.mkDerivation (self: rec {
  version = "0.1";
  name = "condatis-${version}";
  src = "./.";
  everythingFile = "Library.agda";
#   sourceDirectories = [ "./." ];
  buildDepends = [ AgdaStdlib ];
})
