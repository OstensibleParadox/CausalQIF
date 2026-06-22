# MVP Criteria

## MVP 1 — Build split

- Default root `CausalQIF.lean` must compile (or `lake build` should compile when environment permits).
- Active modules imported by default contain no unresolved `sorry`/`admit`.
- Experimental bridge modules stay excluded from the default import set.

## MVP 2 — Canonical structure

- Single canonical root: `CausalQIF` namespace and `causal_qif` package.
- Grouped module structure under:
  - `Graph`, `DSeparation`, `InfoTheory`, `Certificates`, `Examples`
- No duplicate active source roots under different names.

## MVP 3 — Certificate stack

- Finite graph and information lemmas available to prove a finite cut-set-style upper bound.
- Red/blue witness examples in examples and certificates remain syntactically connected through active imports.

## MVP 4 — Archive discipline

- Historical dual-certificate, CasualQIF, and POPL27 material has been cleaned
  from active workspace trees after migration.
- Archive copies are not part of current canonical workspace.

## MVP 5 — Documentation coherence

- `docs/LEAN.md` states scope and boundary assumptions.
- `docs/THEOREM_DEPENDENCIES.md` tracks the active proof stack.
- `docs/ROADMAP.md` records the split (`MarkovGenerator` → `GlobalMarkov`).
- `provenance/MIGRATION_MANIFEST.md` records source, destination, role, and rationale for migrated/archived content.

## Acceptance note

Until the environment provides `lake`, verification is by static checks documented below:

- no forbidden imports under active path
- no stale absolute `/Users/` references in docs
- no unresolved `sorry` in non-experimental Lean files
