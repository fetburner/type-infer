#!/usr/bin/env bash
set -eux

coqc --version
opam --version
opam list --installed --columns=name,version

# Use the repository snapshot and dependencies bundled in the pinned image.
# Do not update opam repositories during verification.
opam pin add coq-type-infer . --kind=path --no-action -y
opam install coq-type-infer --deps-only -y
opam install coq-type-infer -v -y
