import CausalQIF.DSeparation.UnsafeBridge

open Finset
open scoped BigOperators

namespace CausalQIF.GlobalMarkov

noncomputable section

/--
Bridging theorem for the global Markov step.

This is an intermediate, auditable step: the algebraic graphoid machinery plus the
local Markov property is wired through `UnsafeBridge` while this file records the
audited callsite explicitly.  The marked theorem here remains the highest-priority
replacement target for a direct proof in this repository.
-/
theorem localMarkov_dsep_global_CIAlg
    {G : DAG} {Var : ℕ → Type}
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]
    (P : FinitePMF (UnsafeBridge.Assignment G Var))
    (hlocal : UnsafeBridge.LocalMarkov G Var P)
    (hgraphoid : UnsafeBridge.GraphoidCI (UnsafeBridge.CIAlgOnNodes (G := G) (Var := Var) P))
    {X Y Z : Finset ℕ}
    (hquery : DSeparationQuery X Y Z)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hsep : dSeparates G X Y Z) :
    UnsafeBridge.CIAlg P X Y Z hnodes := by
  -- Audited boundary: this theorem is currently a direct lift from the unsafe
  -- bridge module while a full graph-theoretic proof is being completed.
  exact UnsafeBridge.localMarkov_dsep_global_CIAlg (G := G) (Var := Var)
    P hlocal hgraphoid hquery hnodes hsep

end
