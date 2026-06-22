import CausalQIF.DSeparation.MarkovGenerator

open Finset

noncomputable section

namespace InfoTheory

open CausalQIF

/-- Reindex an `(A, B, C)` distribution as `(A, C, B)` so the existing
    `condMutualInfo` API, which is `I(first; second | third)`, represents
    `I(A; C | B)`. -/
def equivACB {α β γ : Type} : α × γ × β ≃ α × β × γ where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv := by
    intro x
    rcases x with ⟨a, c, b⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨a, b, c⟩
    rfl

/-- The `(A, C, B)` view of a PMF originally indexed as `(A, B, C)`. -/
def pmfACB {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ)) : FinitePMF (α × γ × β) :=
  FinitePMF.comapEquiv equivACB P

/-- Conditional mutual information `I(A; C | B)` for a PMF indexed as
    `(A, B, C)`, implemented by reusing `condMutualInfo` on `(A, C, B)`. -/
def I_A_cond_C_B {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ)) : ℝ :=
  condMutualInfo (pmfACB P)

/-- Marginal mass of the middle coordinate `B` from `P(A, B, C)`. -/
def marginalB {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ)) (b : β) : ℝ :=
  ∑ a : α, ∑ c : γ, P.pmf (a, b, c)

/-- Joint marginal mass of `(A, B)` from `P(A, B, C)`. -/
def marginalAB {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ)) (ab : α × β) : ℝ :=
  ∑ c : γ, P.pmf (ab.1, ab.2, c)

/-- Joint marginal mass of `(B, C)` from `P(A, B, C)`. -/
def marginalBC {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ)) (bc : β × γ) : ℝ :=
  ∑ a : α, P.pmf (a, bc.1, bc.2)

/-- Markov chain condition `A -> B -> C`, i.e. `A` and `C` are conditionally
    independent given `B`: `P(a,b,c) * P(b) = P(a,b) * P(b,c)`. -/
def IsMarkovChain {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b c,
    P.pmf (a, b, c) * marginalB P b =
      marginalAB P (a, b) * marginalBC P (b, c)

/-- `I(A; C | B) = 0` under the Markov chain `A -> B -> C`. -/
theorem cond_mutual_info_zero_of_markov {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ))
    (hMC : IsMarkovChain P) :
    I_A_cond_C_B P = 0 := by
  unfold I_A_cond_C_B
  refine condMutualInfo_eq_zero_of_condIndep (pmfACB P) ?_
  intro a c b
  simpa [pmfACB, FinitePMF.comapEquiv, equivACB, marginalB, marginalAB, marginalBC,
    marginalTripleThd, marginalTripleFstThd, marginalTripleSndThd] using hMC a b c

end InfoTheory

namespace CausalQIF

open InfoTheory

/-
The projection bridges for three- and four-variable CI are defined in
`CausalQIF.MarkovGenerator`; this file keeps the compatibility layer for the
downstream theorems that use them.
-/

/-- **d-separation implies conditional independence** in the 3-variable
    algebraic form, using the positive-model projection API. -/
theorem isMarkovChain_of_positiveModel_dsep {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (hquery : DSeparationQuery ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (h_dsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ)) :
    IsMarkovChain (project3PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
  exact isMarkovChain_of_CIExp_project3 M hnodes
    (dsep_implies_CI M hquery hnodes h_dsep)

/-- Full first-arrow bridge consumed by the downstream DPI/KKT cut-set chain:
    d-separation implies zero conditional mutual information, via the already
    proved `cond_mutual_info_zero_of_markov`. -/
theorem cmi_zero_of_positiveModel_dsep {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (hquery : DSeparationQuery ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (h_dsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ)) :
    I_A_cond_C_B (project3PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) = 0 :=
  cond_mutual_info_zero_of_markov
    (project3PMF M (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)))
    (isMarkovChain_of_positiveModel_dsep M hquery hnodes h_dsep)

-- `condMarkov_of_positiveModel_dsep_fourVar` is available unchanged from
-- `CausalQIF.MarkovGenerator` under this same import chain.

example {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {G : DAG} (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (hquery : DSeparationQuery ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (hsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ)) :
    IsMarkovChain (project3PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) :=
  isMarkovChain_of_positiveModel_dsep M hquery hnodes hsep

end CausalQIF

end
