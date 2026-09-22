#!/usr/bin/env bash
set -euo pipefail

# Run from any directory. The reference statements and the submitted proofs
# are separate modules in the same pinned Lake project.
repoDir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

resolveTool() {
  local tool
  tool="$(command -v "$1")" || {
    printf 'Missing executable: %s\n' "$1" >&2
    return 1
  }
  realpath "$tool"
}

# Override the executable paths with the environment variables below.
comparatorHome="$HOME/tools/comparator-euler-4.34"
comparatorBin="$(resolveTool "${COMPARATOR_BIN:-$comparatorHome/.lake/build/bin/comparator}")"
exporterBin="$(resolveTool "${COMPARATOR_LEAN4EXPORT:-$comparatorHome/.lake/packages/lean4export/.lake/build/bin/lean4export}")"
landrunBin="$(resolveTool "${COMPARATOR_LANDRUN:-$HOME/tools/landrun-euler-review/landrun}")"
lakeBin="$(resolveTool lake)"

if [ "$(id -u)" -eq 0 ]; then
  printf 'Run Comparator as an ordinary user, not root.\n' >&2
  exit 1
fi

# Upstream recommends blocking Unix sockets around Landrun. Do not silently
# fall back to an unsandboxed run when systemd or this restriction is unavailable.
exec systemd-run --user --wait --pipe --collect \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --working-directory="$repoDir" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LEAN4EXPORT=$exporterBin" \
  --setenv="COMPARATOR_LANDRUN=$landrunBin" \
  --setenv="LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4}" \
  "$lakeBin" env "$comparatorBin" "$repoDir/comparator.json"
