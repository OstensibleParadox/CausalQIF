# CausalQIF

This repository is the canonical workspace for the finite typed Lean artifact in
the CausalQIF project.

## Canonical structure

```text
CausalQIF/
  lean/
    lakefile.lean         # package: causal_qif
    lean-toolchain
    CausalQIF.lean        # default entry module
    CausalQIF/
      Graph/
      DSeparation/
      InfoTheory/
      Certificates/
      Examples/
      Experimental/
  docs/
    LEAN.md
    THEOREM_DEPENDENCIES.md
    ROADMAP.md
    MVP.md
  experiments/
    harness/
    toy-deployments/
    certificates/
    outputs/
  paper/
    main/
    supplement/
    figures/
  provenance/
    MIGRATION_MANIFEST.md
```

## Lean package and namespace

- Lean package: `causal_qif`
- Lean namespace/library: `CausalQIF`
- Default import path: `import CausalQIF`
- Legacy namespaces (`FiniteQuerySandbox`, `CasualQIF`) are preserved only in
  migration history, not as active workspace trees.

## Source-of-truth policy

- `lean/CausalQIF.lean` is the build root for the active target.
- `lean/CausalQIF/Experimental/*` is excluded from the default build until
  bridge obligations are fully discharged.
- Legacy archive directories are not kept as active workspace trees after
  cleanup.

## Quick commands

- `cd lean && lake build` : compile active target (requires local Lean toolchain)
- `rg -n "FiniteQuerySandbox|CasualQIF|\\bDSeparation\\b" lean/CausalQIF` :
  check for stale root references in active code
- `rg -n "/Users/" docs` :
  ensure no stale absolute paths remain in documentation
- `rg -n "\\bsorry\\b|\\badmit\\b" lean/CausalQIF` :
  verify active modules are free of placeholders (Experimental module excluded)
- `rg -n "^\\s*axiom" lean/CausalQIF/DSeparation/UnsafeBridge.lean` :
  verify unresolved assumptions on the explicit bridge boundary

## Current bridge posture

- `DSeparation/UnsafeBridge.lean` is the single repository location still
  carrying explicit bridge axioms for this proof frontier (`5` axioms total).
- `DSeparation/GlobalMarkov.lean` is the explicit intermediate step for the local
  Markov + graphoid → global d-separation bridge.
- `DSeparation/MarkovGenerator.lean` and `DSeparation/DSepCMIBridge.lean`
  keep the public API shape while avoiding direct axiom declarations.

## Documentation entry points

- `docs/LEAN.md`: scope, build boundaries, active assumptions
- `docs/THEOREM_DEPENDENCIES.md`: active dependency map
- `docs/ROADMAP.md`: migration and proof milestones
- `docs/MVP.md`: acceptance criteria
- `provenance/MIGRATION_MANIFEST.md`: source→destination mapping and rationale
