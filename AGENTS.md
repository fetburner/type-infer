# Project summary

This is a Coq formalisation of Algorithm W for an ML subset, covering soundness and completeness of type inference and type safety. Proofs are in `theories/*.v`; the package is `coq-type-infer`.

## Verification

GitHub Actions tests Coq 8.16.1, 8.18.0, and 8.19.2 with MathComp SSReflect 1.19.0, the successful combinations with MathComp 1.19.0 in the [compatibility experiment](https://github.com/fetburner/type-infer/actions/runs/45751376882). CI runs in native GitHub Actions job containers, using the [verified root-checkout/coq-build approach](https://github.com/fetburner/type-infer/actions/runs/45754523835): checkout runs as root to access runner-owned files; the build runs as `coq` in a temporary source copy with `HOME=/home/coq`. The explicit Git safe-directory setting is scoped to the checked-out workspace.

Locally, run `bash scripts/run-verification.sh [version]` (default: 8.19.2); Docker is required. CI and the local script pin the same tested image digests, and both invoke `scripts/verify.sh` to build and install the package via opam/Dune. Keep the matrix images and local script pins in sync.

## Upgrade boundaries

The historical Coq 8.8–8.12 matrix was used for the initial CI port. The dependency-only upgrade targets Coq 8.16, 8.18–8.19 and MathComp 1.19 without changes to `theories/*.v`. Coq 8.17 is excluded for now because its tested release failed on the deprecated instance locality diagnostic.

Treat further upgrades to Coq 8.20, MathComp 2.x (Hierarchy Builder), and Rocq 9.x as separate changes. Keep CI green at each step and update dependency constraints, the pinned verification image, and the generated opam metadata together.
