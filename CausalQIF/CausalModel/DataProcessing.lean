import CausalQIF.Probability.Entropy

open Finset
open scoped BigOperators Real

namespace CausalQIF.CausalModel

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

open Probability

/-- **Conditional Data Processing Inequality**.
    If X-Y-Z is a Markov chain given W, then I(X;Z|W) ≤ I(Y;Z|W). -/
theorem cond_dpi (P : FinitePMF (α × β × γ × δ)) (h : condMarkov P) :
    condMutualInfo (pmfXZW P) ≤ condMutualInfo (pmfYZW P) := by
  have h_chain_x : condMutualInfo (pmfXZW P) + condMutualInfo (pmfYZXW P) = condMutualInfo (pmfYZW P) + condMutualInfo (pmfXZYW P) := by
    rw [condMutualInfo_pmfXZW, condMutualInfo_pmfYZXW, condMutualInfo_pmfYZW, condMutualInfo_pmfXZYW]
    ring
  have h_nonneg := I_YZ_XW_nonneg P
  have h_zero := I_XZ_YW_eq_zero_of_condMarkov P h
  rw [h_zero] at h_chain_x
  linarith

end

end CausalQIF.CausalModel
