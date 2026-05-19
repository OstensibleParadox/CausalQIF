import CausalQIF.Graph.DirectedAcyclic
import CausalQIF.Graph.Reachability
import CausalQIF.Graph.Moralization
import CausalQIF.DSeparation.Path.Trail
import CausalQIF.DSeparation.MAGWalk
import CausalQIF.DSeparation.Equivalence
import CausalQIF.Probability.FinitePMF
import CausalQIF.Probability.Entropy
import CausalQIF.Probability.Markov
import CausalQIF.CausalModel.Factorization
import CausalQIF.InformationFlow.CutSetBound
import CausalQIF.InformationFlow.ChannelCapacity
import CausalQIF.Main

/-!
# CausalQIF

A clean Lean 4 library for causal inference with quantitative information flow.

## Main Results

- `DAG.dSeparated`: Graph-theoretic d-separation criterion
- `MAGWalk`: Moralized ancestral graph walk certificates
- `dSeparates`: Trail-based d-separation predicate
- `FactorizesOverDAG`: Semantic DAG factorization
- `condMutualInfo_eq_zero_of_factorizes_of_dSeparates`: D-sep → CMI = 0 bridge
- `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le`: Main theorem

## Module Hierarchy

```
CausalQIF/
├── Graph/
│   ├── DirectedAcyclic.lean
│   ├── Reachability.lean
│   └── Moralization.lean
├── DSeparation/
│   ├── Path/
│   │   └── Trail.lean
│   ├── MAGWalk.lean
│   └── Equivalence.lean
├── Probability/
│   ├── FinitePMF.lean
│   ├── Entropy.lean
│   └── Markov.lean
├── CausalModel/
│   └── Factorization.lean
├── InformationFlow/
│   ├── CutSetBound.lean
│   └── ChannelCapacity.lean
└── Main.lean
```
-/
