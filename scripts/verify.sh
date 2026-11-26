#!/usr/bin/env bash
set -eux

coqc --version
opam --version

# No `opam update`: today's opam-repository no longer ships
# ocaml-variants.4.07.1+flambda, so updating breaks the switch
# invariant and the solver fails (exit 20). Use the repo state
# bundled in the image instead.
opam pin add coq-type-infer . --kind=path --no-action -y
opam install coq-type-infer --deps-only -y
opam install coq-type-infer -v -y
