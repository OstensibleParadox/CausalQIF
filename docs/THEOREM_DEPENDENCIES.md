# Theorem Dependency Map

This map tracks the active dependency structure in the canonical `lean/CausalQIF` build.

## Core entrypoint

- `lean/CausalQIF.lean`
  - imports `CausalQIF.Certificates.Tools`
  - imports canonical graph, finite information, certificates, and paper-facing layers
  - imports `CausalQIF.Graph.MarkovBridge`
  - imports certificate families used by the artifact
    (`IdentifiabilityGap`, `DynamicProbeBound`, `StaticCutBound`, `PACLowerBound`, and support modules)
  - imports `CausalQIF.Examples.LinearChain`
  - imports `CausalQIF.Paper.MainTheorems`

## Graph layer

- `Graph/*`
  - provides finite DAG structures, ancestry helpers, and moralization
  - consumed by `CausalQIF.DSeparation`

- `DSeparation/*` (legacy-compatible bridge split)
  - provides trail/active-path graph-search lemmas, trail blocking, and bridge lemmas to probabilistic assumptions
  - consumed by `Certificates` and higher-level certificate modules
  - dependencies: `Graph`, `Finset`, and `Mathlib` combinatorics
  - bridge split:
    `MarkovGenerator` → `GlobalMarkov` → `UnsafeBridge`, and compatibility
    wrappers are re-exported through `DSeparation.DSepCMIBridge` and
    `Graph.MarkovBridge`.

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

`Experimental/InfoTheoryBridge` and `Experimental/FiniteQueryAudit` are retained for
compatibility and traceability and are **not** imported by `lean/CausalQIF.lean`.
Their compatibility theorems are intentionally preserved for historical API
consumers while canonical paper-facing bridges live in `Graph.MarkovBridge` and
`Paper.Compatibility`.
- `Certificates/PredictabilityRouteImpossibility` is a legacy off-root compatibility
  module for the old predictability surrogate. It is not imported by `lean/CausalQIF.lean`
  and is not the paper-facing EIS theorem.
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

The active build is `0 sorry / 5 axiom` (all explicit assumptions currently
reside in `DSeparation/UnsafeBridge.lean`). `CIAlgOnNodes` now carries an
explicit graph-domain witness rather than quantifying over all containment
proofs, so out-of-graph node sets no longer make CI premises vacuously true. The
generic `CIExp ↔ CIAlg` conversion and the 3- and 4-variable tuple-projection
bridges are now proved by finite-assignment projection lemmas in
`UnsafeBridge.lean`; the remaining explicit assumptions are the algebraic
graphoid closure laws and the global local-Markov-to-d-separation bridge. Where
a result's force depends
on an externally-supplied hypothesis (not discharged in Lean), it is listed
here. These are the bridge reductions carried forward into the premise ledger:
They are **reductions**, not closed obligations; paper statements must surface the premise.

| Result | Carried premise (the actual hard part) |
| --- | --- |
| `InfoTheory/DPI.cond_dpi`, `Certificates/DualCertificate.prop2_dynamic_lb` | `condMarkov P` (conditional Markov structure) |
| `Certificates/DualCertificate.{condMarkov_deterministicProbePMF, prop2_dynamic_lb_deterministic_probe}` | deterministic probe construction `probe : State → Trace → Probe`; no external `condMarkov` premise |
| `Certificates/DualCertificate.prop1_static_ub` | `I_S_M_cond_Ttilde P ≤ C_cut Ω` (cut-set capacity bound) |
| `Certificates/CutSetBoundExtract.{cut_set_dpi_bound, abstract_cut_set_bound}` | `condMarkov (pmf_from_vars …)` + capacity bound |
| `DSeparation/DSepCMIBridge.cmi_zero_of_positiveModel_dsep` | `PositiveMarkovModel` + `DSeparationQuery` + `dSeparates` for the 3-variable tuple projection; the tuple projection itself is proved in `UnsafeBridge.isMarkovChain_of_CIExp_project3`, while the route still depends on the remaining graphoid closure and global Markov bridge assumptions |
| `Certificates/PACBounds.theorem3_pac_lower_bound` | `PACPaperStatisticalDerivation` fields: Gaussian KL/Fano bound + missed-cell bound, with formulas recorded in Lean and probability proofs supplied by `provenance/fano_bound.md` |
| `Certificates/EntropicEIS.no_entropic_eis_autoregressive` | deterministic screenability `S = recon(T)`; the finite-Shannon residual-autonomy contradiction is exact |
| `Certificates/PredictabilityRouteImpossibility.internal_route_impossibility_predictability` | legacy off-root `IsPredictable` surrogate + non-σ-additive `ProbSpace`, not `H(I\|T)>0` |

Scope notes:
- d-separation: soundness proven only under pairwise-disjoint `X/Y/Z`; the unrestricted
  biconditional is proven **false** (`dsep_complete_endpoint_in_Z_counterexample`). General
  probabilistic `d-sep ⇒ CI` is exposed through `Graph.MarkovBridge` compatibility
  shims and is not discharged in the current core assumptions.
- `Certificates/ChannelCapacity` is a **KKT upper-bound certificate checker**
  (`capacity_le_of_kkt`), not a channel capacity (no sup over input distributions).
