#!/usr/bin/env bash
set -eu

COQ_VERSION="${1:-8.20.1}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Pin the same tested image digests as the CI matrix.
case "${COQ_VERSION}" in
  8.16|8.16.1)
    IMAGE="mathcomp/mathcomp:2.2.0-coq-8.16@sha256:a73d9bc7cc058a02f69eb74422d45aeb518c993f7a0500c6d7587db6923683b7"
    ;;
  8.18|8.18.0)
    IMAGE="mathcomp/mathcomp:2.2.0-coq-8.18@sha256:74242573b1261215d0c01783f2f32adc5fbb982f09c97890aecee98f327e2a1b"
    ;;
  8.19|8.19.2)
    IMAGE="mathcomp/mathcomp:2.2.0-coq-8.19@sha256:4528ca6551316685d24b8e4468db981224e7da2507c0d683262363ab50151a86"
    ;;
  8.20|8.20.1)
    IMAGE="mathcomp/mathcomp:2.2.0-coq-8.20@sha256:22627a3f9ce8e0670b044465e6e461d4048d8005a4ad919aa73f3eda12ccf8ca"
    ;;
  *)
    echo "Unsupported Coq version: ${COQ_VERSION} (expected 8.16.1, 8.18.0, 8.19.2, or 8.20.1)" >&2
    exit 1
    ;;
esac

# opam path pins build an internal copy, so the source can remain read-only.
docker run --rm -v "${REPO_ROOT}:/home/project:ro" -w /home/project "${IMAGE}" /bin/bash --login -c "bash scripts/verify.sh"
