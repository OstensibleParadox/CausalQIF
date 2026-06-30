#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$repo_root/lean"

lake build
lake env lean CausalQIF/test_import.lean

set +e
rg_output="$(rg -n "Experimental.InfoTheoryBridge|import CausalQIF.Experimental" CausalQIF.lean CausalQIF 2>&1)"
rg_status=$?
set -e

case "$rg_status" in
  0)
    printf '%s\n' "$rg_output"
    printf '%s\n' "error: default Lean build chain must not reference Experimental.InfoTheoryBridge or import CausalQIF.Experimental" >&2
    exit 1
    ;;
  1)
    ;;
  *)
    printf '%s\n' "$rg_output" >&2
    exit "$rg_status"
    ;;
esac
