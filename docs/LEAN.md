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
  CausalQIF.lean           # default root import (compatibility root)
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

`lean/CausalQIF.lean` is the active default entrypoint and imports the compatibility experimental modules listed below.

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

`InfoTheoryBridge` is kept imported in the root for API compatibility but currently provides a compatibility boundary, not a closed bridge from DAG to generic finite-model conditional independence.
`FiniteQueryAudit` is retained as historical bridge logic and is not paper-facing.

## Build target expectation

- Default `lake build` checks modules reachable from `CausalQIF.lean`.
- Imported experimental modules are included in the import graph but intentionally not treated as closed core assumptions.
- Archive directories are build-isolated (`archive/*`, `provenance/*`).
- Active Lean source should contain no references to legacy roots:
  `FiniteQuerySandbox`, `CasualQIF`, or legacy standalone `DSeparation` roots.

For the dependency map and migration notes, see:
- `docs/THEOREM_DEPENDENCIES.md`
- `provenance/MIGRATION_MANIFEST.md`

## 优先级 1 / 2 重点复核（按目录分组）

以下命题已按你提供的清单映射到现有文件位置。每条目前用于“先读”的判断理由是：它们承担关键图论-信息论桥接链路，且不只是直接算术化简；其中绝大多数定理是正式非平凡证明入口，而非 API 兼容壳。

### 优先级 1：最值得先看的命题

文件：`lean/CausalQIF/DSeparation/DAG.lean`
- `DSeparationQuery_iff_DisjointSets`
- `collider_mem_ancestralSubgraphNodes_of_active`
- `first_forward_target_mem_ancestral_of_active`
- `dSeparationGraph_adj_of_mag_single`
- `dSeparationGraph_adj_of_mag_jump`
- `MAGWalk.to_dSeparationGraph_reachable`
- `mag_single_or_jump_of_dSeparationGraph_adj`
- `MAGWalk.of_dSeparationGraph_reachable`
- `magWalk_iff_dSeparationGraph_reachable`
- `MAGWalk.jump_of_active_collider`
- `MAGWalk.single_of_bayesBallStep`
- `MAGWalk.jump_of_bayesBall_collider`
- `MAGWalk.trans_jump_of_bayesBall_collider`
- `magWalk_of_bayesBall_pair`
- `magWalk_of_bayesBall`
- `dSeparationGraph_reachable_of_active_trail_disjoint`
- `dsep_complete_of_endpoint_disjoint`
- `dsep_complete_of_query`
- `dSeparated_of_dSeparated_disjoint`
- `dsep_complete_endpoint_in_Z_counterexample`
- `not_forall_dsep_complete`
- `not_forall_dsep_iff`

文件：`lean/CausalQIF/InfoTheory/InfoTheoryHelpers.lean`
- `negMulLog2_nonneg_lemma`
- `entropy_nonneg`
- `entropyOf_mul_log2`
- `marginalAB_pullback`
- `marginalBC_pullback`
- `marginalB_pullback`
- `chain_rule_I_A_BC`
- `chain_rule_I_A_BC_alt`
- `mutual_info_chain_rule`
- `cond_mutual_info_zero_of_markov`
- `I_A_cond_B_C_nonneg`
- `data_processing_inequality`

文件：`lean/CausalQIF/Examples/CaseStudy.lean`
- `h_total_one`
- `marginalWMass_unit_one`
- `entropyOf_marginalWMass_unit_zero`
- `marginalZMass_unit_sum_one`
- `marginalYZWMass_eq_marginalYZPMF_of_unit_pmf`
- `marginalZWMass_eq_marginalZMass_unit`
- `entropyOf_marginalYWMass_eq_entropyOf_marginalYMass`
- `entropyOf_marginalZWMass_eq_entropyOf_marginalZMass_unit`
- `entropyOf_marginalYZWMass_eq_entropyOf_marginalYZPMF`
- `I_YZ_W_unit_le_entropyOf_marginalYMass`
- `I_YZ_W_unit_CutVar2_le_one`
- `condMarkov_of_SM_indep_and_Omega_depends_only_on_S`
- `linear_chain_cut_set_bound`
- `linear_chain_cut_set_bound_from_dag`

文件：`lean/CausalQIF/InfoTheory/Conditional.lean`
- `condProductMass_pos_of_pmf_ne_zero`
- `condProductMass_sum_fiber`
- `condProductMass_sum_one`
- `sum_pmf_log_marginalTripleFstThd`
- `sum_pmf_log_marginalTripleSndThd`
- `sum_pmf_log_marginalTripleThd`
- `condMutualInfo_kl_identity`
- `condMutualInfo_nonneg`
- `condMutualInfo_eq_zero_of_condIndep`

文件：`lean/CausalQIF/Certificates/IdentifiabilityGap.lean`
- `entropy_sum_dirac`
- `entropy_sum_inj`
- `entropyOf_pair`
- `entropyOf_triple`
- `entropy_sum_image`
- `identifiability_gap_extremes`

文件：`lean/CausalQIF/InfoTheory/MutualInfo.lean`
- `productMarginalMass_pos_of_pmf_ne_zero`
- `productMarginalMass_sum_one`
- `sum_pmf_log_marginalLeftMass`
- `sum_pmf_log_marginalRightMass`
- `condEntropy_mul_log2`
- `condEntropy_nonneg`
- `mutualInfo_kl_identity`
- `mutualInfo_nonneg`

文件：`lean/CausalQIF/InfoTheory/Entropy.lean`
- `negMulLog2_nonneg`
- `entropy_nonneg`
- `entropyOf_equiv_eq`
- `entropyOf_mul_log2`
- `entropy_le_log_card`

文件：`lean/CausalQIF/Certificates/DualCertificate.lean`
- `prop2_dynamic_lb`
- `aggregated_dynamic_lb`
- `visibleMissingMass_sum_one`
- `static_decomposition`
- `missingMass_sum_one`
- `condEntropy_M_cond_Ttilde_le_H_M`
- `I_S_M_cond_Ttilde_le_condEntropy_M_cond_Ttilde`
- `I_S_M_cond_Ttilde_le_H_M`
- `H_M_le_log_card_M`
- `prop1_static_ub_bounded`
- `prop1_static_ub`
- `corollary_additive_ub`

### 优先级 2：次高候选

文件：`lean/CausalQIF/Graph/Ancestry.lean`
- `reachable_equiv_reachableFinset`
- `deleteLeaf_card_lt`
- `mem_ancestors_self`
- `mem_ancestralSubgraphNodes_of_mem`
- `mem_ancestors_of_hasEdge_of_mem_ancestors`
- `mem_ancestralSubgraphNodes_of_hasEdge_left`

文件：`lean/CausalQIF/DSeparation/BayesBall.lean`
- `required_first_target_of_outOf`
- `required_rest_of_outOf`
- `BayesBallStep.of_active_triple`
- `bayesBallReachable_of_active_trail_from_prev`
- `bayesBallReachable_of_active_trail`
- `Trail.startOpen_outOf_of_not_mem`
- `bayesBallReachable_of_active_trail_outOf`
- `not_mem_Z_of_active_noncollider`
- `not_mem_Z_of_active_directional_noncollider`

文件：`lean/CausalQIF/DSeparation/Trail.lean`
- `directionalTripleBlocked_iff_tripleBlocked`
- `HasTriple.cons`
- `TrailBlocked.cons`
- `not_trailBlocked_tail_of_not_trailBlocked_cons`
- `trailBlocked_of_head_tripleBlocked`
- `not_tripleBlocked_head_of_not_trailBlocked`
- `HasTriple.head_of_trail`
- `trailBlocked_of_head_tripleBlocked_trail`
- `not_tripleBlocked_head_of_not_trailBlocked_trail`

文件：`lean/CausalQIF/Certificates/CutSetBoundExtract.lean`
- `pmf_from_vars_apply`
- `marginalXWMass_eq_stateVisibleMass`
- `marginalWMass_eq_visibleMass`
- `marginalZWMass_eq_visibleMissingMass_swap`
- `marginalXZWMass_eq_P_swap`
- `I_original_eq_I_XZ_W_pmf_from_vars`
- `cut_set_dpi_bound`
- `abstract_cut_set_bound`
- `prop1_static_ub_from_cut`

文件：`lean/CausalQIF/InfoTheory/DPI.lean`
- `I_XY_Z_W_eq_I_XZ_W_add_I_YZ_XW`
- `I_XY_Z_W_eq_I_YZ_W_add_I_XZ_YW`
- `condMutualInfo_pmfYZXW`
- `condMutualInfo_pmfXZYW`
- `I_YZ_XW_nonneg`
- `I_XZ_YW_eq_zero_of_condMarkov`
- `cond_dpi`
