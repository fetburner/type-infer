#!/usr/bin/env bash
set -eu

COQ_VERSION="${1:-8.19.2}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Pin the images that compiled all unchanged proofs in the compatibility experiment.
case "${COQ_VERSION}" in
  8.16|8.16.1)
    IMAGE="mathcomp/mathcomp:1.19.0-coq-8.16@sha256:928fcf2009527b0bffdbdf72766012922758bebf764ee30d3582920f14702b57"
    ;;
  8.18|8.18.0)
    IMAGE="mathcomp/mathcomp:1.19.0-coq-8.18@sha256:33227713fd4f8617259a3c382eadced1b51e23d7966fa2f43914ccc7ad056238"
    ;;
  8.19|8.19.2)
    IMAGE="mathcomp/mathcomp:1.19.0-coq-8.19@sha256:820e58054bcdd31eaeec2d023a585f99bbee742771a363fe8931b49643bb7a6c"
    ;;
  *)
    echo "Unsupported Coq version: ${COQ_VERSION} (expected 8.16.1, 8.18.0, or 8.19.2)" >&2
    exit 1
    ;;
esac

# opam path pins build an internal copy, so the source can remain read-only.
docker run --rm -v "${REPO_ROOT}:/home/project:ro" -w /home/project "${IMAGE}" /bin/bash --login -c "bash scripts/verify.sh"
