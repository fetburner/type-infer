#!/usr/bin/env bash
set -eu

ROCQ_VERSION="${1:-9.1.1}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Pin the same tested image digests as the CI matrix.
case "${ROCQ_VERSION}" in
  9.0|9.0.1)
    IMAGE="mathcomp/mathcomp:2.6.0-rocq-prover-9.0@sha256:53e9ef2c3d85068a2e4c7db84da72faffcef08351107911bab48117fec3247bb"
    ;;
  9.1|9.1.1)
    IMAGE="mathcomp/mathcomp:2.6.0-rocq-prover-9.1@sha256:170e09d5ec507180f9ef93cd9e0ba1b58f422e34df50044462170b26807231b9"
    ;;
  9.2|9.2.0)
    IMAGE="mathcomp/mathcomp:2.6.0-rocq-prover-9.2@sha256:a4e066dbe94d40fbbefc2ab7692abb905011a053d1a5434ababee659ffe293e8"
    ;;
  9.3|9.3.0)
    IMAGE="mathcomp/mathcomp:2.6.0-rocq-prover-9.3@sha256:6bf12b95e479f557c1a83cbe602975e84155ec8e9676a84403cf23b65f8f9842"
    ;;
  *)
    echo "Unsupported Rocq version: ${ROCQ_VERSION} (expected 9.0.1, 9.1.1, 9.2.0, or 9.3.0)" >&2
    exit 1
    ;;
esac

# opam path pins build an internal copy, so the source can remain read-only.
docker run --rm --platform linux/amd64 -v "${REPO_ROOT}:/home/project:ro" -w /home/project "${IMAGE}" /bin/bash --login -c "bash scripts/verify.sh"
