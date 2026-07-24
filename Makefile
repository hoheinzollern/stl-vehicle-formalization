# Build the STL-Vehicle Rocq formalization.
# Requires Rocq 9.1 with MathComp 2.5 and mathcomp-analysis 1.16
# (e.g. via opam; run `eval $(opam env)` first, or use the pinned
# Nix toolchain: `nix-build`).

COQMAKEFILE := Makefile.coq

.DEFAULT_GOAL := all

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) install

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) cleanall; fi
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all install clean
