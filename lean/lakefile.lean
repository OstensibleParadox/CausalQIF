import Lake
open Lake DSL

package causal_qif where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Pinned to the rev already resolved in lake-manifest.json for reproducible builds.
-- Bump deliberately via `lake update mathlib`; do not leave floating.
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0e265f2ff3987cdc4757407f55f3dbfc06d52ab5"

@[default_target]
lean_lib CausalQIF
