#!/usr/bin/env bash
set -eu

COQ_VERSION="${1:-8.12}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# opam path pins build an internal copy; Travis's chown granted unused write access.
docker run --rm -v "${REPO_ROOT}:/home/project:ro" -w /home/project "coqorg/coq:${COQ_VERSION}" /bin/bash --login -c "bash scripts/verify.sh"
