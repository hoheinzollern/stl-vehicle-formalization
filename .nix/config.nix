{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "stl-vehicle-formalization";

  ## Rocq 9.1 (hierarchy-builder is broken for 9.2 in the pinned nixpkgs,
  ## and mathcomp-analysis needs it), with MathComp 2.5.0 and
  ## mathcomp-analysis 1.16.0.
  default-bundle = "9.1";

  bundles."9.1" = {
    rocqPackages = {
      rocq-core.override.version = "9.1";
      mathcomp.override.version = "2.5.0";
      mathcomp-analysis.override.version = "1.16.0";
      mathcomp-analysis.job = true;
    };
    coqPackages = {
      coq.override.version = "9.1";
      mathcomp.override.version = "2.5.0";
      mathcomp-analysis.override.version = "1.16.0";
      mathcomp-analysis.job = true;
    };
  };

  ## Cachix caches to use (binary substituters for coq + mathcomp),
  ## so builds are fast rather than compiling everything from source.
  cachix.coq = { };
  cachix.math-comp = { };
}
