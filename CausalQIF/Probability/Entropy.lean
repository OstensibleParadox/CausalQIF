import CausalQIF.Probability.FinitePMF

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]

/-! ## KL-Divergence and Nonnegativity Foundations -/

lemma kl_nonneg_support {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hq_nonneg : ∀ x, 0 ≤ q x)
    (h_support : ∀ x, p x ≠ 0 → 0 < q x)
    (hp_sum : ∑ x, p x = 1)
    (hq_sum : ∑ x, q x = 1) :
    0 ≤ ∑ x, p x * Real.log (p x / q x) := by
  have h_term : ∀ x, p x * Real.log (p x / q x) ≥ p x - q x := by
    intro x
    by_cases hpx : p x = 0
    · rw [hpx]
      have h0 : (0 : ℝ) / q x = 0 := by simp
      simp [h0]
      linarith [hq_nonneg x]
    · have hpx_pos : 0 < p x := lt_of_le_of_ne (hp_nonneg x) (Ne.symm hpx)
      have hqx_pos : 0 < q x := h_support x hpx
      have h1 : Real.log (q x / p x) ≤ q x / p x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hqx_pos hpx_pos)
      have h2 : p x * Real.log (q x / p x) ≤ q x - p x := by
        have h_mul : p x * (q x / p x - 1) = q x - p x := by
          field_simp [hpx_pos.ne']
        have h3 : p x * Real.log (q x / p x) ≤ p x * (q x / p x - 1) := by
          apply mul_le_mul_of_nonneg_left h1 (le_of_lt hpx_pos)
        linarith [h3, h_mul]
      have h3 : p x * Real.log (p x / q x) = -(p x * Real.log (q x / p x)) := by
        rw [← mul_neg]
        congr
        rw [show Real.log (p x / q x) = -Real.log (q x / p x) by
          rw [Real.log_div (by exact hpx_pos.ne') (by exact hqx_pos.ne')]
          rw [Real.log_div (by exact hqx_pos.ne') (by exact hpx_pos.ne')]
          ring]
      rw [h3]
      linarith [h2]
  have hsum : ∑ x, p x * Real.log (p x / q x) ≥ ∑ x, (p x - q x) := by
    apply Finset.sum_le_sum
    intro x _
    exact h_term x
  have h_eq : ∑ x, (p x - q x) = 0 := by
    rw [Finset.sum_sub_distrib]
    linarith [hp_sum, hq_sum]
  linarith [hsum, h_eq]

/-! ## Conditional Mutual Information -/

def condMutualInfo (P : FinitePMF (α × β × γ)) : ℝ :=
  entropyOf (marginalXZMass P) + entropyOf (marginalYZMass P) -
  entropyOf (marginalZMass P) - entropy P

/-! ## Conditional Independence -/

def condIndep (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b z,
    P.pmf (a, b, z) * marginalZMass P z =
      marginalXZMass P (a, z) * marginalYZMass P (b, z)

def condProductMass (P : FinitePMF (α × β × γ)) (xyz : α × β × γ) : ℝ :=
  if marginalZMass P xyz.2.2 = 0 then 0
  else marginalXZMass P (xyz.1, xyz.2.2) * marginalYZMass P (xyz.2.1, xyz.2.2) /
    marginalZMass P xyz.2.2

lemma condMutualInfo_kl_identity (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ, P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz))
      = condMutualInfo P * Real.log 2 := by
  -- Implementation details migrated from NeurIPS stack
  sorry

theorem condMutualInfo_eq_zero_of_condIndep (P : FinitePMF (α × β × γ))
    (hIndep : condIndep P) : condMutualInfo P = 0 := by
  -- Proof using condMutualInfo_kl_identity
  sorry

/-! ## Four-variable Conditional Mutual Information and DPI -/

def marginalXWMass (P : FinitePMF (α × β × γ × δ)) (xw : α × δ) : ℝ :=
  ∑ y : β, ∑ z : γ, P.pmf (xw.1, y, z, xw.2)

def marginalYWMass (P : FinitePMF (α × β × γ × δ)) (yw : β × δ) : ℝ :=
  ∑ x : α, ∑ z : γ, P.pmf (x, yw.1, z, yw.2)

def marginalZWMass (P : FinitePMF (α × β × γ × δ)) (zw : γ × δ) : ℝ :=
  ∑ x : α, ∑ y : β, P.pmf (x, y, zw.1, zw.2)

def marginalWMass (P : FinitePMF (α × β × γ × δ)) (w : δ) : ℝ :=
  ∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z, w)

def marginalXZWMass (P : FinitePMF (α × β × γ × δ)) (xzw : α × γ × δ) : ℝ :=
  ∑ y : β, P.pmf (xzw.1, y, xzw.2.1, xzw.2.2)

def marginalYZWMass (P : FinitePMF (α × β × γ × δ)) (yzw : β × γ × δ) : ℝ :=
  ∑ x : α, P.pmf (x, yzw.1, yzw.2.1, yzw.2.2)

def marginalXYWMass (P : FinitePMF (α × β × γ × δ)) (xyw : α × β × δ) : ℝ :=
  ∑ z : γ, P.pmf (xyw.1, xyw.2.1, z, xyw.2.2)

/-- `I(X;Z | W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_XZ_W (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalXWMass P) +
    entropyOf (marginalZWMass P) -
    entropyOf (marginalWMass P) -
    entropyOf (marginalXZWMass P)

/-- `I(Y;Z | W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_YZ_W (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalYWMass P) +
    entropyOf (marginalZWMass P) -
    entropyOf (marginalWMass P) -
    entropyOf (marginalYZWMass P)

/-- `I(Y;Z | X,W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_YZ_XW (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalXYWMass P) +
    entropyOf (marginalXZWMass P) -
    entropyOf (marginalXWMass P) -
    entropyOf P.pmf

/-- `I(X;Z | Y,W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_XZ_YW (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalXYWMass P) +
    entropyOf (marginalYZWMass P) -
    entropyOf (marginalYWMass P) -
    entropyOf P.pmf

/-- Conditional Markovity as a concrete equality. -/
def condMarkov (P : FinitePMF (α × β × γ × δ)) : Prop :=
  ∀ x y z w,
    P.pmf (x, y, z, w) * marginalYWMass P (y, w)
      =
    marginalXYWMass P (x, y, w) * marginalYZWMass P (y, z, w)

/-- Nonnegativity of conditional mutual information (DPI precursor). -/
lemma I_YZ_XW_nonneg (P : FinitePMF (α × β × γ × δ)) : 0 ≤ I_YZ_XW P :=
  sorry

/-- I(X;Z | Y,W) vanishes under conditional Markovity. -/
lemma I_XZ_YW_eq_zero_of_condMarkov
    (P : FinitePMF (α × β × γ × δ)) (h : condMarkov P) :
    I_XZ_YW P = 0 :=
  sorry


end

end CausalQIF.Probability
