# Lean 4 Formalization: CausalQIF Core

This repository is the canonical Lean source for finite, typed deployment-certificate reasoning.

- Scope: finite discrete graphs, explicit interfaces, explicit Markov/channel assumptions.
- Not claimed scope: real-world alignment certification, continuous-state dynamics, or non-finite guarantees.
- Public root: `CausalQIF`.

## Canonical Lean layout

```text
lean/
  lakefile.lean            # package name: causal_qif
  lean-toolchain
  CausalQIF.lean           # default root import (no experimental bridge modules)
  CausalQIF/
    Certificates/
    DSeparation/
    Experimental/
    Graph/
    InfoTheory/
    Examples/
```

## Package identity

- Package name: `causal_qif`
- Library name: `CausalQIF`
- Default import root: `CausalQIF`
- Public namespace: `CausalQIF`

`lean/CausalQIF.lean` is the active default entrypoint; `experimental` modules are intentionally excluded.

## Current active theorem stack

1. Graph abstraction:
   `Graph` and `DSeparation` define finite DAG objects, trail/active-path search,
   and reachability composition.
2. Information theory:
   `InfoTheory` proves finite-PMF identities for entropy, mutual information, and DPI-like lemmas.
3. Certificates:
   `Certificates` combines cut-set extraction, impossibility, and finite upper-bound statements.
4. Examples:
   `Examples.CaseStudy` provides sanity checks on minimal typed deployments.

## Experimental boundary

Pending bridge obligations are kept under:

- `lean/CausalQIF/Experimental/InfoTheoryBridge.lean`
- `lean/CausalQIF/Experimental/FiniteQueryAudit.lean`

These files are intentionally not imported by the default target until assumptions are formally discharged.

## Build target expectation

- Default `lake build` checks only active modules reachable from `CausalQIF.lean`.
- Archive directories are build-isolated (`archive/*`, `provenance/*`).
- Active Lean source should contain no references to legacy roots:
  `FiniteQuerySandbox`, `CasualQIF`, or legacy standalone `DSeparation` roots.

For the dependency map and migration notes, see:
- `docs/THEOREM_DEPENDENCIES.md`
- `provenance/MIGRATION_MANIFEST.md`
