import CausalQIF.DSeparation.MarkovGenerator

open Finset

namespace CausalQIF.Experimental

noncomputable section

/-!
# Information-theory bridge (experimental)

This module contains the bridge from d-separation to conditional independence.
The bridge is typed over strictly-positive finite Markov models on dependent
graph assignments; this module keeps the historical experimental theorem name
as a compatibility wrapper.
-/

/-- Historical bridge name, now specialized to the typed positive-model API. -/
theorem dSeparation_implies_conditional_independence
    {G : DAG} {Var : ℕ → Type}
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]
    {X Y Z : Finset ℕ} (M : PositiveMarkovModel G Var)
    (hquery : DSeparationQuery X Y Z)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hsep : dSeparates G X Y Z) :
    CIExp M.P X Y Z hnodes :=
  dsep_implies_CI M hquery hnodes hsep

end

end CausalQIF.Experimental
