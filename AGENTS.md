# Project summary

This is a Coq formalisation of Algorithm W for an ML subset, covering soundness and completeness of type inference and type safety. Proofs are in `theories/*.v`; the package is `coq-type-infer`.

## Verification

GitHub Actions tests Coq 8.16.1, 8.18.0, 8.19.2, and 8.20.1 with MathComp SSReflect 2.2.0, the one MathComp 2.x release with images for all four. CI runs in native GitHub Actions job containers, using the [verified root-checkout/coq-build approach](https://github.com/fetburner/type-infer/actions/runs/45754523835): checkout runs as root to access runner-owned files; the build runs as `coq` in a temporary source copy with `HOME=/home/coq`. The explicit Git safe-directory setting is scoped to the checked-out workspace.

Locally, run `bash scripts/run-verification.sh [version]` (default: 8.20.1); Docker is required (the images are amd64-only; on Apple Silicon they run under emulation). CI and the local script pin the same tested image digests, and both invoke `scripts/verify.sh` to build and install the package via opam/Dune. Keep the matrix images and local script pins in sync.

`scripts/verify.sh` also kernel-checks the installed library with `coqchk -o` and fails if the context summary names any `TypeInfer` constant: an `Admitted` proof, an axiom, or a bypassed guard/positivity check. Never leave `Admitted`, `admit`, or new axioms in `theories/*.v`.

## Local development

The local toolchain targets the Rocq 9.1 upgrade: the opam switch `type-infer` has Rocq 9.1, MathComp 2.6.0, and coq-lsp 0.2.5+9.1. Until that upgrade lands, `master` does not build there (Rocq 9 no longer loads `PeanoNat` and friends in the prelude); use `scripts/run-verification.sh` for the CI versions. One-time setup:

```sh
opam switch create type-infer ocaml-base-compiler.4.14.2 --no-switch \
  --repos=default,rocq-released=https://rocq-prover.org/opam/released
opam install --switch=type-infer dune rocq-prover coq-lsp.0.2.5+9.1 coq-mathcomp-ssreflect.2.6.0
git clone --depth 1 --branch 0.2.0 https://github.com/LLM4Rocq/rocq-mcp .rocq-mcp/src
uv venv --python 3.12 .rocq-mcp/venv
uv pip install --python .rocq-mcp/venv/bin/python ./.rocq-mcp/src
```

Build with `opam exec --switch=type-infer -- dune build`. The `rocq` MCP server (`.mcp.json` for Claude Code, `.codex/config.toml` for Codex) runs rocq-mcp in that switch: read proof goals with `rocq_start`, `rocq_check`, and `rocq_step_multi` instead of guessing tactics, then confirm with `dune build`. Dune in that switch rewrites the formatting of `coq-type-infer.opam`; do not commit that diff on its own.

## Upgrade boundaries

The historical Coq 8.8–8.12 matrix was used for the initial CI port. The dependency-only upgrade targets Coq 8.16, 8.18–8.19 and MathComp 1.19 without changes to `theories/*.v`. Coq 8.17 is excluded for now because its tested release failed on the deprecated instance locality diagnostic.

Coq 8.20 no longer infers typeclass arguments of lemmas named in `auto`/`eauto using` clauses ([coq/coq#18909](https://github.com/coq/coq/pull/18909)). `theories/Term.v` therefore uses `pose proof foo; eauto` instead of `eauto using foo` for lemmas that take `Rename`/`Subst` instances; keep that form in new proofs.

MathComp 2 declares structures with Hierarchy Builder: `theories/Types.v` registers `typ` as an `eqType` via `HB.instance Definition _ := hasDecEq.Build typ typ_eqP`; use that form, not the removed `EqMixin`/`EqType`, for new instances.

Treat the Rocq 9.x upgrade (with MathComp 2.4+) as a separate change. Keep CI green at each step and update dependency constraints, the pinned verification image, and the generated opam metadata together.
