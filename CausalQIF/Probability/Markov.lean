import CausalQIF.Probability.Entropy

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## Markov Chain Definitions -/

def marginalTriple_Snd (P : FinitePMF (α × β × γ)) (b : β) : ℝ :=
  ∑ a : α, ∑ c : γ, P.pmf (a, b, c)

def marginalTriple_FstSnd (P : FinitePMF (α × β × γ)) (ab : α × β) : ℝ :=
  ∑ c : γ, P.pmf (ab.1, ab.2, c)


def IsMarkovChain (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b c,
    P.pmf (a, b, c) * marginalTriple_Snd P b =
      marginalTriple_FstSnd P (a, b) * marginalTriple_SndThd P (b, c)

/-! ## CMI=0 for Markov Chains -/

def equivACB : (α × γ × β) ≃ (α × β × γ) where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv := by intro; rfl
  right_inv := by intro; rfl

def pmfACB (P : FinitePMF (α × β × γ)) : FinitePMF (α × γ × β) :=
  FinitePMF.comapEquiv equivACB.symm P

theorem condMutualInfo_eq_zero_of_isMarkovChain (P : FinitePMF (α × β × γ))
    (hMC : IsMarkovChain P) : condMutualInfo (pmfACB P) = 0 := by
  refine condMutualInfo_eq_zero_of_condIndep (pmfACB P) ?_
  intro a c b
  simpa [pmfACB, FinitePMF.comapEquiv, equivACB, marginalTriple_Snd, marginalTriple_FstSnd, marginalTriple_SndThd,
    marginalTriple_Thd, marginalTriple_FstThd, marginalTriple_SndThd] using hMC a b c

end

end CausalQIF.Probability
