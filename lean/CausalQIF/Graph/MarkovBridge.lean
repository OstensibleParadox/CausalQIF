import CausalQIF.DSeparation.DSepCMIBridge

/-
# Markov-Bridge Layer

Canonical bridge exports from the d-separation to conditional-independence
elements.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

namespace Graph

open scoped Real

/-! Compatibility name preserved for the typed positive-model bridge from DAG d-separation. -/
theorem dSeparation_implies_conditional_independence
    {G : DAG} {Var : ℕ → Type}
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]
    {X Y Z : Finset ℕ} (M : PositiveMarkovModel G Var)
    (hquery : DSeparationQuery X Y Z)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hsep : dSeparates G X Y Z) :
    CIExp M.P X Y Z hnodes :=
  dsep_implies_CI M hquery hnodes hsep

export InfoTheory (equivACB pmfACB I_A_cond_C_B marginalB marginalAB marginalBC
  cond_mutual_info_zero_of_markov IsMarkovChain)
export CausalQIF (isMarkovChain_of_positiveModel_dsep
  cmi_zero_of_positiveModel_dsep condMarkov_of_positiveModel_dsep_fourVar
  Tuple3Var Tuple4Var PositiveMarkovModel dsep_implies_CI)

end Graph

end CausalQIF
