#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
project_root="$(cd "${script_dir}/.." && pwd)"
cd "${project_root}"

if command -v lake >/dev/null 2>&1; then
  lake_command=(lake)
else
  elan_root="${ELAN_HOME:-${HOME}/.elan}"
  if [[ ! -x "${elan_root}/bin/lake" ]]; then
    echo "lake was not found on PATH or under ${elan_root}/bin" >&2
    echo "Install Elan from https://lean-lang.org/lean4/doc/quickstart.html" >&2
    exit 1
  fi
  lake_command=("${elan_root}/bin/lake")
fi

echo "=== Weighted Hensel Repair verification ==="
echo "Commit: $(git rev-parse HEAD)"
echo "Lean: $("${lake_command[@]}" env lean --version)"
echo

echo "=== Building terminal theorem dependency graph ==="
"${lake_command[@]}" build WeightedHensel.Terminal

echo
echo "=== Replaying headline theorem and axiom report ==="
"${lake_command[@]}" env lean Main.lean

echo
echo "=== Checking repository hygiene ==="
git diff --check

forbidden='(^|[^[:alnum:]_])(sorry|admit|sorryAx|axiom|native_decide)([^[:alnum:]_]|$)'
if grep -RInE "${forbidden}" --include='*.lean' \
    WeightedHensel Main.lean WeightedHensel.lean; then
  echo "Forbidden proof token found"
  exit 1
fi

if grep -RInE '^import[[:space:]]+Aspis' --include='*.lean' \
    WeightedHensel Main.lean WeightedHensel.lean; then
  echo "Aspis dependency found"
  exit 1
fi

if grep -InE 'aspis' lakefile.toml lake-manifest.json; then
  echo "Aspis package dependency found"
  exit 1
fi

echo
echo "PASS: weighted Hensel repair"
