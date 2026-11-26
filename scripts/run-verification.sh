#!/usr/bin/env bash
set -eu

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# Pin the image that compiled all unchanged proofs in the compatibility experiment.
IMAGE="mathcomp/mathcomp:1.19.0-coq-8.19@sha256:820e58054bcdd31eaeec2d023a585f99bbee742771a363fe8931b49643bb7a6c"

# opam path pins build an internal copy, so the source can remain read-only.
docker run --rm -v "${REPO_ROOT}:/home/project:ro" -w /home/project "${IMAGE}" /bin/bash --login -c "bash scripts/verify.sh"
