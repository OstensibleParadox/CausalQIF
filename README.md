# CausalQIF

A Lean 4 library for causal inference with quantitative information flow.

## Main Results

- `DAG.dSeparated`: Graph-theoretic d-separation criterion
- `MAGWalk`: Moralized ancestral graph walk certificates
- `dSeparates`: Trail-based d-separation predicate
- `FactorizesOverDAG`: Semantic DAG factorization
- `isMarkovChain_of_productFactorizes_chain3`: Product-factorized chain instance → Markov chain
- `condMutualInfo_eq_zero_of_isMarkovChain`: Markov chain → CMI = 0
- `CausalModel.condMutualInfo_eq_zero_of_factorizes_of_dSeparates`: D-sep → CMI = 0 bridge
- `cond_dpi`: Conditional data processing inequality
- `condMutualInfo_le_of_dual_witness`: Dual KL witness → CMI upper bound
- `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`: Main cut-set leakage bound
- `certified_leakage_gap_of_dSeparated_graph`: H(S∣T̃) ≤ H(S∣T_full) + C
- `stateLeakage_le_of_dual_witness`: Cut-set leakage bound from a dual witness

## Module Hierarchy

```
CausalQIF/
├── Graph/
│   ├── DirectedAcyclic.lean
│   ├── Reachability.lean
│   └── Moralization.lean
├── DSeparation/
│   ├── ActiveRoute.lean
│   ├── BayesBall/
│   │   ├── Basic.lean
│   └── ... (see CausalQIF.lean for full hierarchy)
├── Probability/
│   ├── FinitePMF.lean
│   ├── Entropy.lean
│   └── Markov.lean
├── CausalModel/
│   ├── Factorization.lean
│   ├── ProductFactorization.lean
│   └── DataProcessing.lean
├── InformationFlow/
│   ├── CutSetBound.lean
│   ├── Duality.lean
│   └── ChannelCapacity.lean
├── Examples/
│   └── LinearChain.lean
└── Main.lean
```

## Usage

Ensure you have the appropriate Lean 4 toolchain installed (see `lean-toolchain`).
To build:
```bash
lake build
```

## License
MIT
