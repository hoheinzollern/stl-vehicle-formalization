{ lib, mkRocqDerivation, mathcomp-analysis, version ? null }:

with lib; mkRocqDerivation {
  pname = "stl-vehicle-formalization";
  owner = "hoheinzollern";
  inherit version;

  # Build from clean sources: never copy generated Rocq artifacts
  # (a stale Makefile.coq would hardcode the wrong rocq-runtime path).
  src = cleanSourceWith {
    src = cleanSource ./../../..;
    filter = path: _type:
      let b = baseNameOf path; in
      ! (hasSuffix ".vo" b || hasSuffix ".vok" b || hasSuffix ".vos" b
         || hasSuffix ".glob" b || hasSuffix ".aux" b
         || b == "Makefile.coq" || b == "Makefile.coq.conf"
         || b == ".Makefile.coq.d");
  };

  propagatedBuildInputs = [ mathcomp-analysis ];

  meta = {
    description = "Rocq formalization of the Reuse theorem (Vehicle with Time)";
    license = lib.licenses.mit;
  };
}
