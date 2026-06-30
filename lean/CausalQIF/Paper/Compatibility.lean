import CausalQIF.Graph.MarkovBridge

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
  CausalQIF.Graph.dSeparation_implies_conditional_independence
    M hquery hnodes hsep

end Compatibility

end Paper

end CausalQIF
