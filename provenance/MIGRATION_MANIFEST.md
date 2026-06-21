# Migration Manifest

Purpose: record the source, destination, role, and rationale for the canonicalization.

All paths are relative to this repository root.

## Active Promotion

| Source | Destination | Role | Reason |
|---|---|---|---|
| `../math/dual-certificate/lean4/FiniteQuerySandbox.lean` | `lean/CausalQIF.lean` | Canonical entrypoint | Replace legacy root entry file and align package naming with `CausalQIF`. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/CMI_Nonneg.lean` | `lean/CausalQIF/Certificates/CMI_Nonneg.lean` | Certificate core lemma | Preserved theorem content under new namespace/module group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/CaseStudy.lean` | `lean/CausalQIF/Examples/CaseStudy.lean` | Active sanity example | Reclassified as example-level demonstration. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/ChannelCapacity.lean` | `lean/CausalQIF/Certificates/ChannelCapacity.lean` | Certificates layer | Unified with certificate namespace. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/CoveringBound.lean` | `lean/CausalQIF/Certificates/CoveringBound.lean` | Certificates layer | Preserved as finite bound theorem body. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/CutSetBoundExtract.lean` | `lean/CausalQIF/Certificates/CutSetBoundExtract.lean` | Certificate extraction | Core theorem family for cut-set extraction in active stack. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAG/Ancestry.lean` | `lean/CausalQIF/Graph/Ancestry.lean` | Graph utilities | Moved into graph namespace (ancestral relationships). |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAG/Basic.lean` | `lean/CausalQIF/Graph/Basic.lean` | Graph utilities | Core DAG primitives for active build. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAG/BayesBall.lean` | `lean/CausalQIF/DSeparation/BayesBall.lean` | D-separation graph search | Re-homed into dedicated d-separation module group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAG/DSeparation.lean` | `lean/CausalQIF/DSeparation/DAG.lean` | D-separation graph search | Semantic core of d-separation reasoning. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAG/Moralization.lean` | `lean/CausalQIF/Graph/Moralization.lean` | Graph utilities | Moralization support for structural rewrites. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAG/Trail.lean` | `lean/CausalQIF/DSeparation/Trail.lean` | D-separation graph search | Active trail/triple machinery under d-separation group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAG/all.lean` | `lean/CausalQIF/DSeparation/all.lean` | Aggregation | Stable module aggregator for d-separation internals. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DAGParser.lean` | `lean/CausalQIF/DSeparation/DAGParser.lean` | Parser | Retained parser in DSeparation group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DSepCMIBridge.lean` | `lean/CausalQIF/DSeparation/DSepCMIBridge.lean` | Bridge shim | Bridge point remains in DSeparation for eventual proof closure. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/DualCertificate.lean` | `lean/CausalQIF/Certificates/DualCertificate.lean` | Certificates layer | Dual certificate statement remains in certificate namespace. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/FiniteQueryAudit.lean` | `lean/CausalQIF/Experimental/FiniteQueryAudit.lean` | Experimental bridge | Kept in Experimental because assumptions are pending. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/FiniteQueryDecisionImpossibility.lean` | `lean/CausalQIF/Certificates/FiniteQueryDecisionImpossibility.lean` | Certificates layer | Preserved theorem family. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/GeometricImpossibility.lean` | `lean/CausalQIF/Certificates/GeometricImpossibility.lean` | Certificates layer | Preserved impossibility theorem family. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/GeometricTools.lean` | `lean/CausalQIF/Certificates/GeometricTools.lean` | Certificates layer | Separated as certificate-support tools. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/IdentifiabilityGap.lean` | `lean/CausalQIF/Certificates/IdentifiabilityGap.lean` | Certificates layer | Explicit identifiability-gap examples in active namespace. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/Impossibility.lean` | `lean/CausalQIF/Certificates/Impossibility.lean` | Certificates layer | Core impossibility statement moved to active certificate group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InternalImpossibility.lean` | `lean/CausalQIF/Certificates/InternalImpossibility.lean` | Certificates layer | Internal impossibility lemmas in certificate group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/MarkovGenerator.lean` | `lean/CausalQIF/DSeparation/MarkovGenerator.lean` | Graph semantics | Markov generation assumptions in DSeparation group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/PACBounds.lean` | `lean/CausalQIF/Certificates/PACBounds.lean` | Certificates layer | Learning-style PAC bound theorems moved to certificates. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/PredictabilityRouteImpossibility.lean` | `lean/CausalQIF/Certificates/PredictabilityRouteImpossibility.lean` | Certificates layer | Predictability-impossibility theorem moved active. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/QuantizedBound.lean` | `lean/CausalQIF/Certificates/QuantizedBound.lean` | Certificates layer | Quantized alphabet bounds grouped in certificates. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/QuotientFactorization.lean` | `lean/CausalQIF/Certificates/QuotientFactorization.lean` | Certificates layer | Maintained in certificate namespace. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/Screenability.lean` | `lean/CausalQIF/Certificates/Screenability.lean` | Certificates layer | Screenability theorems moved to certificates. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/ScreenabilityBridge.lean` | `lean/CausalQIF/Certificates/ScreenabilityBridge.lean` | Certificates layer | Bridge variant retained in certificates until assumptions close. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/SemanticClosureIff.lean` | `lean/CausalQIF/Certificates/SemanticClosureIff.lean` | Certificates layer | Semantic closure equivalence moved with certificates. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/SeparatedPackingImpossibility.lean` | `lean/CausalQIF/Certificates/SeparatedPackingImpossibility.lean` | Certificates layer | Preserved as core impossibility theorem. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/Tools.lean` | `lean/CausalQIF/Certificates/Tools.lean` | Certificates layer | Shared helper utilities moved to certificate namespace. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/TraceRecoverability.lean` | `lean/CausalQIF/Certificates/TraceRecoverability.lean` | Certificates layer | Recovered in active certificate group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/TraceRecoverabilityBridge.lean` | `lean/CausalQIF/Certificates/TraceRecoverabilityBridge.lean` | Certificates layer | Bridge variant retained for compatibility in certificates group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/Basic.lean` | `lean/CausalQIF/InfoTheory/Basic.lean` | Information theory | Core entropy/helper lemmas kept in InfoTheory. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/Conditional.lean` | `lean/CausalQIF/InfoTheory/Conditional.lean` | Information theory | Conditional MI/entropy lemmas. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/DPI.lean` | `lean/CausalQIF/InfoTheory/DPI.lean` | Information theory | DPI-style lemmas in InfoTheory namespace. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/Entropy.lean` | `lean/CausalQIF/InfoTheory/Entropy.lean` | Information theory | Finite entropy infrastructure. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/KL.lean` | `lean/CausalQIF/InfoTheory/KL.lean` | Information theory | KL divergence lemmas in InfoTheory namespace. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/Marginal.lean` | `lean/CausalQIF/InfoTheory/Marginal.lean` | Information theory | Marginal identity lemmas. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/MutualInfo.lean` | `lean/CausalQIF/InfoTheory/MutualInfo.lean` | Information theory | Mutual information identities and inequalities. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory/all.lean` | `lean/CausalQIF/InfoTheory/all.lean` | Aggregation | Maintains stable grouped import. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheoryHelpers.lean` | `lean/CausalQIF/InfoTheory/InfoTheoryHelpers.lean` | Information theory | Helper lemmas for InfoTheory group. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/InfoTheory.lean` | `lean/CausalQIF/InfoTheory/InfoTheory.lean` | Aggregation | Preserved aggregator entrypoint. |
| `../math/dual-certificate/lean4/FiniteQuerySandbox/test_import.lean` | `lean/CausalQIF/test_import.lean` | Smoke test | Lightweight import check for the canonical module tree. |

## Archived Legacy Sources

Historical source trees listed below are part of the migration record only.  
These specific legacy trees were intentionally removed from active build roots.

| Source | Destination | Role | Reason |
|---|---|---|---|
| `../popl27/lean4/` | `(removed)` | Archival | Historical POPL27 formalism retained only in provenance records, excluded from active build. |
| `../archive_memos/CasualQIF/CausalQIF` | `(removed)` | Archival | `CasualQIF` lineage kept for historical context only in migration notes. |

## Documentation migration

| Source | Destination | Role | Reason |
|---|---|---|---|
| `docs/LEAN.md` (existing) | `docs/LEAN.md` | Active doc | Canonicalized from legacy notes into active-build oriented scope statement. |
| `README` references to pre-canonical paths | `README.md` | Active doc update | Updated to point at canonical structure and archive policy. |

## Build boundary note

- `lean/lakefile.lean` and `lean/CausalQIF.lean` are treated as build-control artifacts.
- Experimental files are intentionally excluded from root imports and are documented in `docs/LEAN.md`.
