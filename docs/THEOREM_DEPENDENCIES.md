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
- Legacy archive roots are not part of active builds.

## Canonical check

See the migration manifest for exact moved/archived file mapping:
`provenance/MIGRATION_MANIFEST.md`.

## Canonical results vs. aliases (for theorem counts)

Several modules are **reader-facing re-exports** that are *definitionally equal*
(`theorem alias := canonical`) to a canonical result. They MUST NOT be counted as
independent theorems in any contribution tally.

| Alias module / decl | Canonical source |
| --- | --- |
| `Certificates/TraceRecoverability.{no_internal_witness_trace_recoverability, DeterministicScreen.no_eis_autoregressive}` | `Certificates/Screenability.no_eis_autoregressive` |
| `Certificates/TraceRecoverabilityBridge.no_internal_witness_trace_recoverability_bridge` | `Certificates/Screenability` (via `ScreenabilityBridge`) |
| `Certificates/ScreenabilityBridge.{no_exact_witness_under_screen, no_internal_witness_under_trace_recoverability_bridge}` | `Certificates/Screenability.no_eis_autoregressive` |
| `Certificates/FiniteQueryDecisionImpossibility.finite_query_decision_impossibility` | `Certificates/Impossibility.finite_query_impossibility` |
| `Certificates/SeparatedPackingImpossibility.finite_support_cannot_cover_separated_sequence` | `Certificates/GeometricImpossibility.finite_patch_cannot_cover_separated` |
| `Certificates/QuotientFactorization.semantic_factorization_iff` | `Certificates/SemanticClosureIff.factors_through_quotient_iff` |

## Premise ledger (proved vs. assumed)

The active build is `0 sorry / 0 axiom`. Where a result's force depends on an
externally-supplied hypothesis (not discharged in Lean), it is listed here. These are
**reductions**, not closed obligations; paper statements must surface the premise.

| Result | Carried premise (the actual hard part) |
| --- | --- |
| `InfoTheory/DPI.cond_dpi`, `Certificates/DualCertificate.prop2_dynamic_lb` | `condMarkov P` (conditional Markov structure) |
| `Certificates/DualCertificate.prop1_static_ub` | `I_S_M_cond_Ttilde P ≤ C_cut Ω` (cut-set capacity bound) |
| `Certificates/CutSetBoundExtract.{cut_set_dpi_bound, abstract_cut_set_bound}` | `condMarkov (pmf_from_vars …)` + capacity bound |
| `DSeparation/DSepCMIBridge.cmi_zero_of_factorizes_dsep` | `FactorizesOverDAG` (3-variable algebraic Markov case only) |
| `Certificates/PACBounds.theorem3_pac_lower_bound` | `PACPaperStatisticalDerivation` fields: Gaussian KL/Fano bound + missed-cell bound, with formulas recorded in Lean and probability proofs supplied by `provenance/fano_bound.md` |
| `Certificates/InternalImpossibility.internal_impossibility_predictability` | runs on the `IsPredictable` surrogate + non-σ-additive `ProbSpace`, not `H(I\|T)>0` |

Scope notes:
- d-separation: soundness proven only under pairwise-disjoint `X/Y/Z`; the unrestricted
  biconditional is proven **false** (`dsep_complete_endpoint_in_Z_counterexample`). General
  probabilistic `d-sep ⇒ CI` is the deferred `Experimental/InfoTheoryBridge` `sorry`
  (excluded from the active build).
- `Certificates/ChannelCapacity` is a **KKT upper-bound certificate checker**
  (`capacity_le_of_kkt`), not a channel capacity (no sup over input distributions).
