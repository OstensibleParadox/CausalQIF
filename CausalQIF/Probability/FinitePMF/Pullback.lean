import CausalQIF.Probability.FinitePMF.Marginals

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Pullback Lemmas -/

lemma marginalXZMass_pullback (P : FinitePMF (α × β × γ)) (f : α × γ → ℝ) :
    ∑ xz : α × γ, marginalXZMass P xz * f xz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (a, c) := by
  unfold marginalXZMass
  calc
    ∑ xz : α × γ, (∑ y : β, P.pmf (xz.1, y, xz.2)) * f xz
        = ∑ xz : α × γ, ∑ y : β, P.pmf (xz.1, y, xz.2) * f xz := by
          refine Finset.sum_congr rfl (fun xz _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ y : β, ∑ xz : α × γ, P.pmf (xz.1, y, xz.2) * f xz := by rw [Finset.sum_comm]
    _ = ∑ y : β, ∑ a : α, ∑ c : γ, P.pmf (a, y, c) * f (a, c) := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Fintype.sum_prod_type]
    _ = ∑ a : α, ∑ y : β, ∑ c : γ, P.pmf (a, y, c) * f (a, c) := by rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (a, c) := rfl

lemma marginalYZMass_pullback (P : FinitePMF (α × β × γ)) (f : β × γ → ℝ) :
    ∑ yz : β × γ, marginalYZMass P yz * f yz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (b, c) := by
  unfold marginalYZMass
  calc
    ∑ yz : β × γ, (∑ x : α, P.pmf (x, yz.1, yz.2)) * f yz
        = ∑ yz : β × γ, ∑ x : α, P.pmf (x, yz.1, yz.2) * f yz := by
          refine Finset.sum_congr rfl (fun yz _ => ?_)
          rw [Finset.sum_mul]
    _ = ∑ x : α, ∑ yz : β × γ, P.pmf (x, yz.1, yz.2) * f yz := by rw [Finset.sum_comm]
    _ = ∑ x : α, ∑ b : β, ∑ c : γ, P.pmf (x, b, c) * f (b, c) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Fintype.sum_prod_type]
    _ = ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (b, c) := rfl

lemma marginalZMass_pullback (P : FinitePMF (α × β × γ)) (f : γ → ℝ) :
    ∑ z : γ, marginalZMass P z * f z =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
  unfold marginalZMass
  calc
    ∑ c : γ, (∑ a : α, ∑ b : β, P.pmf (a, b, c)) * f c
        = ∑ c : γ, ∑ a : α, ∑ b : β, P.pmf (a, b, c) * f c := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          simp_rw [Finset.sum_mul]
    _ = ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

end

end CausalQIF.Probability
