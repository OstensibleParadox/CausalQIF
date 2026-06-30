import CausalQIF.Graph.MarkovBridge
import CausalQIF.Examples.LinearChain

/-!
# Paper Compatibility Layer

Compatibility declarations for historical bridge/experimental API names.
This module is intentionally small and paper-facing friendly.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

namespace Paper

namespace Compatibility

-- d-separation bridge kept for legacy compatibility
theorem dSeparation_implies_conditional_independence
    {G : DAG} {Var : ℕ → Type}
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]
    {X Y Z : Finset ℕ} (M : PositiveMarkovModel G Var)
    (hquery : DSeparationQuery X Y Z)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hsep : dSeparates G X Y Z) :
    CIExp M.P X Y Z hnodes :=
  CausalQIF.Graph.theorem2a_bridge
    M hquery hnodes hsep

-- Linear-chain case-study compatibility shim.
@[deprecated linear_chain_cut_set_bound_of_dSeparated (since := "2026-06-30")]
theorem linear_chain_cut_set_bound_from_dag
    (G : DAG)
    (P : FinitePMF (State2 × Unit × Missing2))
    (Ω_vars : (State2 × Unit × Missing2) → CutVar2)
    (M : PositiveMarkovModel G (Tuple4Var State2 CutVar2 Missing2 Unit))
    (hquery : DSeparationQuery ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (hproject :
      project4PMF M
        (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) =
          pmf_from_vars P Ω_vars)
    (h_dsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ)) :
    I_S_M_cond_Ttilde P ≤ 1 :=
  linear_chain_cut_set_bound_of_dSeparated G P Ω_vars M hquery hnodes hproject h_dsep

end Compatibility

end Paper

end CausalQIF
