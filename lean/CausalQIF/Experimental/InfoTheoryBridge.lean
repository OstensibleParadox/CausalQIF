import CausalQIF.DSeparation.all
import CausalQIF.InfoTheory

open Finset

namespace CausalQIF.Experimental

noncomputable section

/-!
# Information-theory bridge (experimental)

This module contains the bridge from d-separation to conditional independence.
It is intentionally isolated from the default build target until the bridge is
fully discharged.
-/

/-- Graph-conditional probability model for a DAG. -/
structure FinitePMFOverDAG (G : DAG) where
  dummy : Unit

/-- Placeholder conditional independence statement over finite graph variables. -/
def ConditionalIndependence {G : DAG} (_P : FinitePMFOverDAG G)
    (_X _Y _Z : Finset ℕ) : Prop :=
  True

/-- Markov compatibility placeholder for a DAG model. -/
def MarkovCompatible {G : DAG} (_P : FinitePMFOverDAG G) (G_orig : DAG) : Prop :=
  ∀ v, v ∈ G_orig.nodes →
    ConditionalIndependence (G := G) _P {v} (G_orig.nodes \ ({v} ∪ descendants G_orig v)) (parents G_orig v)

/-- **Pending bridge theorem**.

This bridge is currently treated as a proof obligation; downstream modules should
only use it intentionally from the `Experimental` namespace.
-/
theorem dSeparation_implies_conditional_independence
    {G : DAG} {X Y Z : Finset ℕ} (P : FinitePMFOverDAG G)
    (hsep : dSeparates G X Y Z)
    (hMarkov : MarkovCompatible P G) :
    ConditionalIndependence P X Y Z := by
  sorry

end CausalQIF.Experimental
