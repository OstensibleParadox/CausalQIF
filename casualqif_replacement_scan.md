# CasualQIF replacement scan

Scope: theorem-level scan of `neurips26/lean4` and `popl27/lean4` against `CasualQIF`.

Legend:
- `moved`: same math, new namespace or file
- `renamed`: old theorem now has a new name
- `split`: old theorem became several newer theorems
- `alias-preserved`: old name still exists as a deprecated alias
- `not ported verbatim`: the old theorem was folded into a more general result or example

## Executive summary

- The quantitative bridge moved into `CasualQIF` and is now split across `Probability`, `CausalModel`, and `InformationFlow`.
- `CasualQIF` keeps several old snake_case names as deprecated aliases, so compatibility is intentionally preserved.
- The main theorem-level migrations are the factorization bridge, the cut-set leakage pipeline, the dual witness bound, and the d-separation equivalence / reverse-synthesis layer.

## `neurips26/lean4`

| Old math family | `CasualQIF` successor | Status | Notes |
| --- | --- | --- | --- |
| Markov blanket generator and local Markov builders (`computeMarkovBlanket`, `generateMarkovConditions`, `generateMarkovBlanketConditions`) | `CausalQIF.Graph.MarkovBlanket.computeMarkovBlanket`, `spouses`, `generateMarkovConditions`, `generateMarkovBlanketConditions` | moved / renamed | Same combinatorics, now generic over `V` and isolated in the graph layer. |
| Semantic DAG factorization bridge (`FactorizesOverDAG`, `factorizes_dsep_implies_cond_indep`, `condMarkov_of_factorizes_dsep_fourVar`) | `CausalQIF.CausalModel.Factorization.FactorizesOverDAG`, `isMarkovChain_of_factorizes_of_dSeparates`, `condMutualInfo_eq_zero_of_factorizes_of_dSeparates`, `condMarkov_of_factorizes_of_dSeparates_fourVar` | split + renamed | The old one-shot bridge is now a typed semantic predicate plus target theorem(s). |
| Markov chain and zero-CMI bridge (`IsMarkovChain`, `cond_mutual_info_zero_of_markov`) | `CausalQIF.Probability.Markov.IsMarkovChain`, `condMutualInfo_eq_zero_of_isMarkovChain` | moved / renamed | Same mathematics, new namespace and naming style. |
| CMI identities and DPI helper layer (`condMutualInfo_kl_identity`, `condMutualInfo_nonneg`, `I_A_cond_B_C_nonneg`, `data_processing_inequality`) | `CausalQIF.Probability.Entropy.Identities.CondMutualInfo.*`, `CausalQIF.CausalModel.DataProcessing.cond_dpi` | moved + split | The old helper-layer proofs are now the core CMI identity file plus the conditional DPI theorem. |
| Cut-set pushforward and DPI bottleneck (`pmf_from_vars`, `I_original_eq_I_XZ_W_pmf_from_vars`, `cut_set_dpi_bound`, `abstract_cut_set_bound`, `prop1_static_ub_from_cut`) | `pmfFromVars`, `pmfFromVars_apply`, `stateLeakage_eq_condMutualInfo_pmfMargOutSnd_pmfFromVars`, `stateLeakage_le_of_cutMutualInfo_le`, `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le` | split + renamed | Old snake_case names remain available as deprecated aliases. |
| Security decomposition and static certificate (`static_decomposition`, `prop1_static_ub`, `prop1_static_ub_bounded`) | `entropy_security_decomposition`, `hSCondTtilde`, `hSCondTfull`, `stateLeakage` | renamed / moved | The old notation was re-expressed in the `InformationFlow` namespace. |
| Channel capacity and KKT certificate (`KKT_Certificate`, `capacity_le_of_kkt`, `KKT_Certificate.of_direct_bound`, `KKT_Certificate.of_dual_witness`) | same names in `CausalQIF.InformationFlow.ChannelCapacity` | moved | Same theorem family, new home. |
| D-separation equivalence and active witness (`dsep_complete_of_endpoint_disjoint`, `dSeparated_of_dSeparated_disjoint`, `dSeparated_iff_dSeparates`, `activeWitness_of_not_dSeparated`) | `CausalQIF.DSeparation.Equivalence.*`, `CausalQIF.DSeparation.TraceSynthesis.Assembly.activeWitness_of_not_dSeparated` | moved | The reverse-synthesis layer was carried over intact. |
| Linear-chain case study (`linear_chain_cut_set_bound`, `linear_chain_cut_set_bound_from_dag`) | `CausalQIF.Main.stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`, `CausalQIF.Examples.LinearChain.linearChain_stateLeakage_le_one_of_dSeparates` | folded into general theorem | The old case-study theorem is not preserved verbatim. |

## `popl27/lean4`

| Old math family | `CasualQIF` successor | Status | Notes |
| --- | --- | --- | --- |
| Placeholder bridge (`dSeparation_implies_conditional_independence`) | `CausalQIF.CausalModel.Factorization.isMarkovChain_of_factorizes_of_dSeparates`, `condMutualInfo_eq_zero_of_factorizes_of_dSeparates`, `condMarkov_of_factorizes_of_dSeparates_fourVar` | replaced by split verified bridge | The `popl27` file is a stub; the proof lives in `CasualQIF`. |
| D-separation equivalence layer (`dsep_complete_of_endpoint_disjoint`, `dSeparated_of_dSeparated_disjoint`, `dSeparated_iff_dSeparates`) | `CausalQIF.DSeparation.Equivalence.*` | moved | Same theorem names, new namespace. |
| Reverse-synthesis witness (`activeWitness_of_not_dSeparated`) | `CausalQIF.DSeparation.TraceSynthesis.Assembly.activeWitness_of_not_dSeparated` | moved | Same theorem name. |
| Product-factorization chain theorem (`isMarkovChain_of_productFactorizes_chain3`) | `CausalQIF.CausalModel.ProductFactorization.isMarkovChain_of_productFactorizes_chain3` | moved | Same theorem name. |
| Dual witness CMI upper bound (`condMutualInfo_le_of_dual_witness`) | `CausalQIF.InformationFlow.Duality.condMutualInfo_le_of_dual_witness` | moved | Same theorem name. |

## Compatibility aliases kept in `CasualQIF`

- `pmf_from_vars` -> `pmfFromVars`
- `H_S_cond_Ttilde` -> `hSCondTtilde`
- `H_S_cond_Tfull` -> `hSCondTfull`
- `marginalTriple_FstSnd` / `marginalTriple_Snd` -> `marginalTripleFstSnd` / `marginalTripleSnd`
- `cond_mutual_info_pair_fst_fth_reshape` / `cond_mutual_info_pair_snd_fth_reshape` -> `condMutualInfo_pmfPairFstFthReshape` / `condMutualInfo_pmfPairSndFthReshape`
- several `marginalQuad_*` aliases remain deprecated for compatibility

## Still local / no direct successor found

- `delta_act`, `prop2_dynamic_lb`, and `aggregated_dynamic_lb` from `neurips26/lean4/FiniteQuerySandbox/DualCertificate.lean` did not show up as theorem-level successors in `CasualQIF`.
- The old `popl27` bridge stub is still a stub there; the verified replacement is split across `CasualQIF.CausalModel`, `CasualQIF.Probability`, and `CasualQIF.InformationFlow`.

## Primary successor files

- `[CasualQIF/CausalQIF.lean](/Users/ostensible_paradox/Documents/CasualQIF/CausalQIF.lean)`
- `[CasualQIF/CausalModel/Factorization.lean](/Users/ostensible_paradox/Documents/CasualQIF/CausalModel/Factorization.lean)`
- `[CasualQIF/CausalModel/ProductFactorization.lean](/Users/ostensible_paradox/Documents/CasualQIF/CausalModel/ProductFactorization.lean)`
- `[CasualQIF/CausalModel/DataProcessing.lean](/Users/ostensible_paradox/Documents/CasualQIF/CausalModel/DataProcessing.lean)`
- `[CasualQIF/Probability/Entropy/Identities/CondMutualInfo.lean](/Users/ostensible_paradox/Documents/CasualQIF/Probability/Entropy/Identities/CondMutualInfo.lean)`
- `[CasualQIF/Probability/Markov.lean](/Users/ostensible_paradox/Documents/CasualQIF/Probability/Markov.lean)`
- `[CasualQIF/InformationFlow/Duality.lean](/Users/ostensible_paradox/Documents/CasualQIF/InformationFlow/Duality.lean)`
- `[CasualQIF/InformationFlow/ChannelCapacity.lean](/Users/ostensible_paradox/Documents/CasualQIF/InformationFlow/ChannelCapacity.lean)`
- `[CasualQIF/InformationFlow/CutSetBound/Defs.lean](/Users/ostensible_paradox/Documents/CasualQIF/InformationFlow/CutSetBound/Defs.lean)`
- `[CasualQIF/InformationFlow/CutSetBound/Basic.lean](/Users/ostensible_paradox/Documents/CasualQIF/InformationFlow/CutSetBound/Basic.lean)`
- `[CasualQIF/InformationFlow/CutSetBound/Lemmas.lean](/Users/ostensible_paradox/Documents/CasualQIF/InformationFlow/CutSetBound/Lemmas.lean)`
- `[CasualQIF/DSeparation/Equivalence.lean](/Users/ostensible_paradox/Documents/CasualQIF/DSeparation/Equivalence.lean)`
- `[CasualQIF/DSeparation/TraceSynthesis/Assembly.lean](/Users/ostensible_paradox/Documents/CasualQIF/DSeparation/TraceSynthesis/Assembly.lean)`
- `[CasualQIF/Graph/MarkovBlanket.lean](/Users/ostensible_paradox/Documents/CasualQIF/Graph/MarkovBlanket.lean)`
- `[CasualQIF/Main.lean](/Users/ostensible_paradox/Documents/CasualQIF/Main.lean)`
- `[CasualQIF/Examples/LinearChain.lean](/Users/ostensible_paradox/Documents/CasualQIF/Examples/LinearChain.lean)`
