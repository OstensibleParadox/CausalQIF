# Theorem Dependency Map

This map tracks the active dependency structure in the canonical `lean/CausalQIF` build.

## Core entrypoint

- `lean/CausalQIF.lean`
  - imports `CausalQIF.Certificates.Tools`
  - imports `CausalQIF.Certificates.CMI_Nonneg`
  - imports `CausalQIF.InfoTheory` (grouped)
  - imports `CausalQIF.Certificates.CutSetBoundExtract`
  - imports `CausalQIF.Certificates.TraceRecoverability` / `TraceRecoverabilityBridge`
  - imports `CausalQIF.Certificates.DualCertificate`
  - imports `CausalQIF.Certificates` family modules
  - imports `CausalQIF.DSeparation.DAGParser`
  - imports `CausalQIF.DSeparation.MarkovGenerator`
  - imports `CausalQIF.DSeparation.DSepCMIBridge`
  - imports `CausalQIF.Examples.CaseStudy`

## Graph layer

- `Graph/*`
  - provides finite DAG structures, ancestry helpers, and moralization
  - consumed by `CausalQIF.DSeparation`

- `DSeparation/*`
  - provides trail/active-path graph-search lemmas, trail blocking, and bridge lemmas to probabilistic assumptions
  - consumed by `Certificates` and higher-level certificate modules
  - dependencies: `Graph`, `Finset`, and `Mathlib` combinatorics

## Information theory layer

- `InfoTheory/*`
  - finite entropy / mutual information / KL / chain rule / DPI infrastructure
  - depends on basic finite PMF lemmas
  - consumed by
    - `DSeparation.DSepCMIBridge`
    - certificate upper bound lemmas
    - case-study reductions

## Certificates layer

- `Certificates/CutSetBoundExtract`
  - identifies marginals and rewrites deployment quantities into abstract information terms
- `Certificates/CMI_Nonneg`, `QuantizedBound`, `ChannelCapacity`
  - core entropy/information identities and bounds used by upper-bounds
- `Certificates/IdentifiabilityGap`, `GeometricTools`, `PACBounds`, `GeometricImpossibility`
  - gap-style constructions and impossibility statements
- `Certificates/*` in general are expected to depend on both `DSeparation` and `InfoTheory`.

## Boundaries / excluded modules

- `Experimental/InfoTheoryBridge` is the explicit pending theorem that should not currently close
  core assumptions.
- `Experimental/FiniteQueryAudit` is historical bridge logic retained for audit traceability only.
- `archive/legacy-*` directories are not part of active builds and are excluded from dependency checks.

## Canonical check

See the migration manifest for exact moved/archived file mapping:
`provenance/MIGRATION_MANIFEST.md`.
