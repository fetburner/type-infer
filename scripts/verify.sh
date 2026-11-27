#!/usr/bin/env bash
set -eux

rocq --version
opam --version
opam list --installed --columns=name,version

# Use the repository snapshot and dependencies bundled in the pinned image;
# only the coq-core compatibility package (coqc/coqdep for Dune) is fetched.
# Do not update opam repositories during verification.
opam pin add coq-type-infer . --kind=path --no-action -y
opam install coq-type-infer --deps-only -y
opam install coq-type-infer -v -y

# Kernel-check the installed library. A TypeInfer name in the summary means an
# Admitted proof, an axiom, or a bypassed guard/positivity check. rocqchk prints
# the summary on stderr.
summary=$(rocqchk -silent -o $(cd theories && for f in *.v; do echo "TypeInfer.${f%.v}"; done) 2>&1)
if grep -F 'TypeInfer.' <<<"$summary"; then exit 1; fi
