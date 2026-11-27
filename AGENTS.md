# Project summary

This is a Rocq (formerly Coq) formalisation of Algorithm W for an ML subset, covering soundness and completeness of type inference and type safety. Proofs are in `theories/*.v`; the package is `coq-type-infer`.

## Verification

GitHub Actions tests Rocq 9.0.1, 9.1.1, 9.2.0, and 9.3.0 with MathComp 2.6.0, the one MathComp release with images for all four. CI runs in native GitHub Actions job containers, using the [verified root-checkout/coq-build approach](https://github.com/fetburner/type-infer/actions/runs/45754523835): checkout runs as root to access runner-owned files; the build runs as the image's `rocq` user in a temporary source copy with `HOME=/home/rocq`. The explicit Git safe-directory setting is scoped to the checked-out workspace.

Locally, run `bash scripts/run-verification.sh [version]` (default: 9.1.1); Docker is required (the images are amd64-only; on Apple Silicon they run under emulation). CI and the local script pin the same tested image digests, and both invoke `scripts/verify.sh` to build and install the package via opam/Dune. Keep the matrix images and local script pins in sync.

`scripts/verify.sh` also kernel-checks the installed library with `rocqchk -o` and fails if the context summary names any `TypeInfer` constant: an `Admitted` proof, an axiom, or a bypassed guard/positivity check. Never leave `Admitted`, `admit`, or new axioms in `theories/*.v`.

## Local development

The opam switch `type-infer` has Rocq 9.1, MathComp 2.6.0, and coq-lsp 0.2.5+9.1, matching the 9.1.1 CI image. One-time setup:

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

The Rocq 9 upgrade dropped Coq 8.x and MathComp 2.2. Rocq 9 no longer loads `PeanoNat` and friends in the prelude: prefer MathComp or Corelib (`From Corelib Require Import Program.Tactics` supplies the `Program` obligation tactic) and import Stdlib explicitly only where needed (`From Stdlib Require Wf_nat`). Import MathComp as `From mathcomp Require Import boot`; `all_ssreflect` and `all_boot` are deprecated in 2.6.0. MathComp 2.4 stopped setting `SsrOldRewriteGoalsOrder` globally, so `Types.v`, `Typing.v`, and `TypeSafety.v` set it locally because their intro patterns assume the main goal comes before rewrite side conditions; keep it in those files.

The MathComp images for Rocq 9.0–9.2 ship Dune 3.17, which has no `rocq` mode, and none of them installs `coqc`/`coqdep`. The package therefore keeps `(using coq 0.2)` and depends on the `coq-core` compatibility package, which `scripts/verify.sh` downloads and installs at verification time, the one dependency the images do not bundle. Move to Dune's `rocq` mode (Dune 3.21+) and drop `coq-core` once every tested image ships a new enough Dune.

Keep CI green at each step and update dependency constraints, the pinned verification image, and the generated opam metadata together.
