# Project summary

This is a Coq formalisation of Algorithm W for an ML subset, covering soundness and completeness of type inference and type safety. Proofs are in `theories/*.v`; the package is `coq-type-infer`.

## Verification

GitHub Actions tests Coq 8.16.1, 8.18.0, and 8.19.2 with MathComp SSReflect 1.19.0, the successful combinations with MathComp 1.19.0 in the [compatibility experiment](https://github.com/fetburner/type-infer/actions/runs/45751376882). Locally, run `bash scripts/run-verification.sh [version]` (default: 8.19.2); Docker is required. The script pins each tested image by digest, and `scripts/verify.sh` builds and installs the package via opam/Dune.

## Upgrade boundaries

The historical Coq 8.8–8.12 matrix was used for the initial CI port. The dependency-only upgrade targets Coq 8.16, 8.18–8.19 and MathComp 1.19 without changes to `theories/*.v`. Coq 8.17 is excluded for now because its tested release failed on the deprecated instance locality diagnostic.

Treat further upgrades to Coq 8.20, MathComp 2.x (Hierarchy Builder), and Rocq 9.x as separate changes. Keep CI green at each step and update dependency constraints, the pinned verification image, and the generated opam metadata together.
