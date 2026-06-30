import CausalQIF.Graph.MarkovBridge

namespace CausalQIF.Experimental

noncomputable section

/-!
# Information-theory bridge (experimental)

This module contains the bridge from d-separation to conditional independence.
This module now keeps only the historical compatibility declaration.
-/

/-- Historical bridge name, now specialized to the typed positive-model API. -/
@[deprecated CausalQIF.Graph.theorem2a_bridge (since := "2026-06-30")]
theorem dSeparation_implies_conditional_independence
    {G : DAG} {Var : ℕ → Type}
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]
    {X Y Z : Finset ℕ} (M : PositiveMarkovModel G Var)
  (hquery : DSeparationQuery X Y Z)
  (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
  (hsep : dSeparates G X Y Z) :
  CIExp M.P X Y Z hnodes :=
  CausalQIF.Graph.theorem2a_bridge
    (M := M) hquery hnodes hsep

end

end CausalQIF.Experimental
