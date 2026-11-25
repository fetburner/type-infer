#!/usr/bin/env bash
set -eux

coqc --version
opam --version

opam update
opam pin add coq-type-infer . --kind=path --no-action -y
opam install coq-type-infer --deps-only -y
opam install coq-type-infer -v -y
