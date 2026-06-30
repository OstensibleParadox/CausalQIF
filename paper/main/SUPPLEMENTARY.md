# Supplementary Material -- CausalQIF

This supplement is intentionally scoped to the Lean 4 artifact.

## Build

```bash
cd lean
lake build CausalQIF
```

## Canonical Documentation

- `../../README.md`: repository scope and source-of-truth policy.
- `../../docs/LEAN.md`: Lean layout, imported modules, and active assumptions.
- `../../docs/THEOREM_DEPENDENCIES.md`: dependency map and premise ledger.
- `../../THEOREM_INDEX.csv`: theorem-by-theorem claims, assumptions, and nonclaims.
- `../../provenance/MIGRATION_MANIFEST.md`: migration record for retired roots.

## Artifact Boundary

CausalQIF contains the finite typed proof core: finite PMFs, entropy and
conditional mutual information, conditional DPI, cut-variable reductions,
d-separation bridge modules, and certificate wrappers.  It does not contain
measurement-study code or results, and such results are not part of the Lean
evidence chain.  The infinitesimal Shannon operator manuscript is also outside
this artifact boundary.
