# Project summary

This is a Coq formalisation of Algorithm W for an ML subset, covering soundness and completeness of type inference and type safety. Proofs are in `theories/*.v`; the package is `coq-type-infer`.

## Verification

GitHub Actions tests a matrix of Coq 8.8–8.12. Locally, run `bash scripts/run-verification.sh <version>`; Docker is required. `scripts/verify.sh` is the in-container build shared by both.

## Phase boundaries

Phase 1: CI port only. Versions stay 8.8–8.12. Never modify `theories/*.v`, `dune-project`, or opam constraints as part of CI work.

Phase 2: Upgrade Coq and SSReflect one step at a time, in separate changes, with CI green at each step.

After Phase 2, reconsider replacing the `docker run` wrapper with GitHub Actions job containers; Phase 1 deliberately avoids them because the historical images (Coq 8.8–8.12) may not run current checkout/Node tooling reliably.
