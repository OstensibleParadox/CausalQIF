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
  marginalXZMass P (xyz.1, xyz.2.2) *
    marginalYZMass P (xyz.2.1, xyz.2.2) /
    marginalZMass P xyz.2.2

lemma condProductMass_nonneg (P : FinitePMF (α × β × γ)) (xyz : α × β × γ) :
    0 ≤ condProductMass P xyz := by
  unfold condProductMass
  exact div_nonneg
    (mul_nonneg (marginalXZMass_nonneg P (xyz.1, xyz.2.2))
      (marginalYZMass_nonneg P (xyz.2.1, xyz.2.2)))
    (marginalZMass_nonneg P xyz.2.2)

lemma pmf_le_marginalXZMass (P : FinitePMF (α × β × γ)) (x : α) (y : β) (z : γ) :
    P.pmf (x, y, z) ≤ marginalXZMass P (x, z) := by
  unfold marginalXZMass
  exact Finset.single_le_sum (fun y' _ => P.pmf_nonneg (x, y', z)) (Finset.mem_univ y)

lemma pmf_le_marginalYZMass (P : FinitePMF (α × β × γ)) (x : α) (y : β) (z : γ) :
    P.pmf (x, y, z) ≤ marginalYZMass P (y, z) := by
  unfold marginalYZMass
  exact Finset.single_le_sum (fun x' _ => P.pmf_nonneg (x', y, z)) (Finset.mem_univ x)

lemma marginalXZMass_le_marginalZMass (P : FinitePMF (α × β × γ)) (x : α) (z : γ) :
    marginalXZMass P (x, z) ≤ marginalZMass P z := by
  have h_nonneg : ∀ x : α, 0 ≤ marginalXZMass P (x, z) :=
    fun x => marginalXZMass_nonneg P (x, z)
  have hle : marginalXZMass P (x, z) ≤ ∑ x : α, marginalXZMass P (x, z) :=
    Finset.single_le_sum (fun x _ => h_nonneg x) (Finset.mem_univ x)
  rwa [marginalXZMass_sum_z P z] at hle

lemma condProductMass_pos_of_pmf_ne_zero
    (P : FinitePMF (α × β × γ)) (xyz : α × β × γ)
    (hxyz : P.pmf xyz ≠ 0) :
    0 < condProductMass P xyz := by
  rcases xyz with ⟨x, y, z⟩
  have hp_pos : 0 < P.pmf (x, y, z) :=
    lt_of_le_of_ne (P.pmf_nonneg (x, y, z)) (Ne.symm hxyz)
  have hxz_pos : 0 < marginalXZMass P (x, z) :=
    lt_of_lt_of_le hp_pos (pmf_le_marginalXZMass P x y z)
  have hyz_pos : 0 < marginalYZMass P (y, z) :=
    lt_of_lt_of_le hp_pos (pmf_le_marginalYZMass P x y z)
  have hz_pos : 0 < marginalZMass P z :=
    lt_of_lt_of_le hxz_pos (marginalXZMass_le_marginalZMass P x z)
  unfold condProductMass
  exact div_pos (mul_pos hxz_pos hyz_pos) hz_pos

lemma condProductMass_sum_fiber (P : FinitePMF (α × β × γ)) (z : γ) :
    (∑ x : α, ∑ y : β, condProductMass P (x, y, z)) = marginalZMass P z := by
  by_cases hz : marginalZMass P z = 0
  · have hxz_zero : ∀ x : α, marginalXZMass P (x, z) = 0 := by
      intro x; have hle := marginalXZMass_le_marginalZMass P x z
      have hnonneg := marginalXZMass_nonneg P (x, z); linarith
    simp [condProductMass, hz, hxz_zero]
  · have hz_pos : 0 < marginalZMass P z := lt_of_le_of_ne (marginalZMass_nonneg P z) (Ne.symm hz)
    calc
      (∑ x : α, ∑ y : β, condProductMass P (x, y, z))
          = ∑ x : α, ∑ y : β, marginalXZMass P (x, z) * marginalYZMass P (y, z) / marginalZMass P z := rfl
      _ = ∑ x : α, marginalXZMass P (x, z) := by
            apply Finset.sum_congr rfl; intro x _
            have hterm : ∀ y : β, marginalXZMass P (x, z) * marginalYZMass P (y, z) / marginalZMass P z
                = (marginalXZMass P (x, z) / marginalZMass P z) * marginalYZMass P (y, z) := by
              intro y; field_simp [hz]
            simp_rw [hterm]; rw [← Finset.mul_sum, marginalYZMass_sum_z P z]; field_simp [hz]
      _ = marginalZMass P z := marginalXZMass_sum_z P z

lemma condProductMass_sum_one (P : FinitePMF (α × β × γ)) :
    ∑ xyz : α × β × γ, condProductMass P xyz = 1 := by
  calc
    ∑ xyz : α × β × γ, condProductMass P xyz
        = ∑ x : α, ∑ y : β, ∑ z : γ, condProductMass P (x, y, z) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ x : α, ∑ z : γ, ∑ y : β, condProductMass P (x, y, z) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ z : γ, ∑ x : α, ∑ y : β, condProductMass P (x, y, z) := by
          rw [Finset.sum_comm]
    _ = ∑ z : γ, marginalZMass P z := by apply Finset.sum_congr rfl; intro z _; exact condProductMass_sum_fiber P z
    _ = 1 := marginalZMass_sum_one P

lemma sum_pmf_log_marginalXZMass (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalXZMass P (xyz.1, xyz.2.2)))
      =
    ∑ xz : α × γ, marginalXZMass P xz * Real.log (marginalXZMass P xz) := by
  calc
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalXZMass P (xyz.1, xyz.2.2)))
        = ∑ x : α, ∑ y : β, ∑ z : γ,
            P.pmf (x, y, z) * Real.log (marginalXZMass P (x, z)) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ x : α, ∑ z : γ, ∑ y : β,
            P.pmf (x, y, z) * Real.log (marginalXZMass P (x, z)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ x : α, ∑ z : γ,
            marginalXZMass P (x, z) * Real.log (marginalXZMass P (x, z)) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro z _
          rw [← Finset.sum_mul]
          rfl
    _ = ∑ xz : α × γ, marginalXZMass P xz * Real.log (marginalXZMass P xz) := by
          rw [← Fintype.sum_prod_type' (fun x z =>
            marginalXZMass P (x, z) * Real.log (marginalXZMass P (x, z)))]

lemma sum_pmf_log_marginalYZMass (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalYZMass P (xyz.2.1, xyz.2.2)))
      =
    ∑ yz : β × γ, marginalYZMass P yz * Real.log (marginalYZMass P yz) := by
  calc
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalYZMass P (xyz.2.1, xyz.2.2)))
        = ∑ x : α, ∑ y : β, ∑ z : γ,
            P.pmf (x, y, z) * Real.log (marginalYZMass P (y, z)) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ y : β, ∑ z : γ, ∑ x : α,
            P.pmf (x, y, z) * Real.log (marginalYZMass P (y, z)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_comm]
    _ = ∑ y : β, ∑ z : γ,
            marginalYZMass P (y, z) * Real.log (marginalYZMass P (y, z)) := by
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro z _
          rw [← Finset.sum_mul]
          rfl
    _ = ∑ yz : β × γ, marginalYZMass P yz * Real.log (marginalYZMass P yz) := by
          rw [← Fintype.sum_prod_type' (fun y z =>
            marginalYZMass P (y, z) * Real.log (marginalYZMass P (y, z)))]

lemma sum_pmf_log_marginalZMass (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalZMass P xyz.2.2))
      =
    ∑ z : γ, marginalZMass P z * Real.log (marginalZMass P z) := by
  calc
    (∑ xyz : α × β × γ,
      P.pmf xyz * Real.log (marginalZMass P xyz.2.2))
        = ∑ x : α, ∑ y : β, ∑ z : γ,
            P.pmf (x, y, z) * Real.log (marginalZMass P z) := by
          rw [Fintype.sum_prod_type]
          congr with x
          rw [Fintype.sum_prod_type]
    _ = ∑ x : α, ∑ z : γ, ∑ y : β,
            P.pmf (x, y, z) * Real.log (marginalZMass P z) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ z : γ, ∑ x : α, ∑ y : β,
            P.pmf (x, y, z) * Real.log (marginalZMass P z) := by
          rw [Finset.sum_comm]
    _ = ∑ z : γ,
            marginalZMass P z * Real.log (marginalZMass P z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [show (∑ x : α, ∑ y : β,
              P.pmf (x, y, z) * Real.log (marginalZMass P z))
              =
              ∑ x : α, (∑ y : β, P.pmf (x, y, z)) * Real.log (marginalZMass P z) by
                apply Finset.sum_congr rfl
                intro x _
                rw [← Finset.sum_mul]]
          rw [← Finset.sum_mul]
          rfl

lemma condMutualInfo_kl_identity (P : FinitePMF (α × β × γ)) :
    (∑ xyz : α × β × γ, P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz))
      = condMutualInfo P * Real.log 2 := by
  let A : ℝ := ∑ xyz : α × β × γ, P.pmf xyz * Real.log (P.pmf xyz)
  let B : ℝ := ∑ xz : α × γ, marginalXZMass P xz * Real.log (marginalXZMass P xz)
  let C : ℝ := ∑ yz : β × γ, marginalYZMass P yz * Real.log (marginalYZMass P yz)
  let D : ℝ := ∑ z : γ, marginalZMass P z * Real.log (marginalZMass P z)
  have hterm : ∀ xyz : α × β × γ,
      P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz)
        =
      ((P.pmf xyz * Real.log (P.pmf xyz)
        - P.pmf xyz * Real.log (marginalXZMass P (xyz.1, xyz.2.2)))
        - P.pmf xyz * Real.log (marginalYZMass P (xyz.2.1, xyz.2.2)))
        + P.pmf xyz * Real.log (marginalZMass P xyz.2.2) := by
    intro xyz
    by_cases hxyz : P.pmf xyz = 0
    · simp [hxyz]
    · rcases xyz with ⟨x, y, z⟩
      have hp_pos : 0 < P.pmf (x, y, z) :=
        lt_of_le_of_ne (P.pmf_nonneg (x, y, z)) (Ne.symm hxyz)
      have hxz_pos : 0 < marginalXZMass P (x, z) :=
        lt_of_lt_of_le hp_pos (pmf_le_marginalXZMass P x y z)
      have hyz_pos : 0 < marginalYZMass P (y, z) :=
        lt_of_lt_of_le hp_pos (pmf_le_marginalYZMass P x y z)
      have hz_pos : 0 < marginalZMass P z :=
        lt_of_lt_of_le hxz_pos (marginalXZMass_le_marginalZMass P x z)
      have hq_pos : 0 < condProductMass P (x, y, z) :=
        condProductMass_pos_of_pmf_ne_zero P (x, y, z) hxyz
      have hlogq : Real.log (condProductMass P (x, y, z))
          =
          Real.log (marginalXZMass P (x, z)) +
          Real.log (marginalYZMass P (y, z)) -
          Real.log (marginalZMass P z) := by
        unfold condProductMass
        rw [Real.log_div (mul_ne_zero hxz_pos.ne' hyz_pos.ne') hz_pos.ne']
        rw [Real.log_mul hxz_pos.ne' hyz_pos.ne']
      rw [Real.log_div hp_pos.ne' hq_pos.ne', hlogq]
      ring
  have hsum :
      (∑ xyz : α × β × γ,
        P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz))
        = A - B - C + D := by
    calc
      (∑ xyz : α × β × γ,
        P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz))
          =
        ∑ xyz : α × β × γ,
          (((P.pmf xyz * Real.log (P.pmf xyz)
            - P.pmf xyz * Real.log (marginalXZMass P (xyz.1, xyz.2.2)))
            - P.pmf xyz * Real.log (marginalYZMass P (xyz.2.1, xyz.2.2)))
            + P.pmf xyz * Real.log (marginalZMass P xyz.2.2)) := by
            apply Finset.sum_congr rfl
            intro xyz _
            exact hterm xyz
      _ = A - B - C + D := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
            rw [sum_pmf_log_marginalXZMass P, sum_pmf_log_marginalYZMass P,
              sum_pmf_log_marginalZMass P]
  have hHXZ := entropyOf_mul_log2 (marginalXZMass P)
  have hHYZ := entropyOf_mul_log2 (marginalYZMass P)
  have hHZ := entropyOf_mul_log2 (marginalZMass P)
  have hHXYZ := entropyOf_mul_log2 (fun xyz : α × β × γ => P.pmf xyz)
  have hcmi : condMutualInfo P * Real.log 2 = A - B - C + D := by
    unfold condMutualInfo
    calc
      (entropyOf (marginalXZMass P) + entropyOf (marginalYZMass P) -
          entropyOf (marginalZMass P) -
          entropyOf (fun xyz : α × β × γ => P.pmf xyz)) * Real.log 2
          =
        entropyOf (marginalXZMass P) * Real.log 2 +
          entropyOf (marginalYZMass P) * Real.log 2 -
          entropyOf (marginalZMass P) * Real.log 2 -
          entropyOf (fun xyz : α × β × γ => P.pmf xyz) * Real.log 2 := by
            ring
      _ = A - B - C + D := by
            rw [hHXZ, hHYZ, hHZ, hHXYZ]
            simp [A, B, C, D]
            ring
  rw [hsum, hcmi]

lemma condMutualInfo_nonneg (P : FinitePMF (α × β × γ)) :
    0 ≤ condMutualInfo P := by
  have hkl := kl_nonneg_support P.pmf (condProductMass P)
    P.pmf_nonneg
    (condProductMass_nonneg P)
    (condProductMass_pos_of_pmf_ne_zero P)
    P.sum_one
    (condProductMass_sum_one P)
  rw [condMutualInfo_kl_identity P] at hkl
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  by_contra hneg
  push Not at hneg
  have hmul_neg : condMutualInfo P * Real.log 2 < 0 :=
    mul_neg_of_neg_of_pos hneg hlog2_pos
  linarith

theorem condMutualInfo_eq_zero_of_condIndep (P : FinitePMF (α × β × γ))
    (hIndep : condIndep P) : condMutualInfo P = 0 := by
  have hkl_zero : (∑ xyz : α × β × γ, P.pmf xyz * Real.log (P.pmf xyz / condProductMass P xyz)) = 0 := by
    apply Finset.sum_eq_zero; intro xyz _; by_cases hx : P.pmf xyz = 0
    · simp [hx]
    · rcases xyz with ⟨a, b, z⟩; have h_eq := hIndep a b z
      have hz_pos : 0 < marginalZMass P z := by
        have hp_pos : 0 < P.pmf (a, b, z) := lt_of_le_of_ne (P.pmf_nonneg _) (Ne.symm hx)
        have hXZ_pos : 0 < marginalXZMass P (a, z) := lt_of_lt_of_le hp_pos (pmf_le_marginalXZMass P a b z)
        exact lt_of_lt_of_le hXZ_pos (marginalXZMass_le_marginalZMass P a z)
      have hq_eq : condProductMass P (a, b, z) = P.pmf (a, b, z) := by
        unfold condProductMass; rw [← h_eq]; field_simp [hz_pos.ne']
      simp [hq_eq, hx]
  have hmul := condMutualInfo_kl_identity P
  rw [hkl_zero] at hmul
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hmul.symm).resolve_right hlog2

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

/-- `I((X,Y);Z | W)` for a four-variable PMF `(X,Y,Z,W)`. -/
def I_XY_Z_W (P : FinitePMF (α × β × γ × δ)) : ℝ :=
  entropyOf (marginalXYWMass P) +
    entropyOf (marginalZWMass P) -
    entropyOf (marginalWMass P) -
    entropyOf P.pmf

lemma I_XY_Z_W_eq_I_XZ_W_add_I_YZ_XW (P : FinitePMF (α × β × γ × δ)) :
    I_XY_Z_W P = I_XZ_W P + I_YZ_XW P := by
  unfold I_XY_Z_W I_XZ_W I_YZ_XW
  ring

lemma I_XY_Z_W_eq_I_YZ_W_add_I_XZ_YW (P : FinitePMF (α × β × γ × δ)) :
    I_XY_Z_W P = I_YZ_W P + I_XZ_YW P := by
  unfold I_XY_Z_W I_YZ_W I_XZ_YW
  ring

def equivYZXW : β × γ × (α × δ) ≃ α × β × γ × δ where
  toFun t := (t.2.2.1, t.1, t.2.1, t.2.2.2)
  invFun t := (t.2.1, t.2.2.1, (t.1, t.2.2.2))
  left_inv := by
    intro t
    rcases t with ⟨y, z, x, w⟩
    rfl
  right_inv := by
    intro t
    rcases t with ⟨x, y, z, w⟩
    rfl

def equivXZYW : α × γ × (β × δ) ≃ α × β × γ × δ where
  toFun t := (t.1, t.2.2.1, t.2.1, t.2.2.2)
  invFun t := (t.1, t.2.2.1, (t.2.1, t.2.2.2))
  left_inv := by
    intro t
    rcases t with ⟨x, z, y, w⟩
    rfl
  right_inv := by
    intro t
    rcases t with ⟨x, y, z, w⟩
    rfl

def pmfYZXW (P : FinitePMF (α × β × γ × δ)) :
    FinitePMF (β × γ × (α × δ)) :=
  FinitePMF.comapEquiv equivYZXW P

def pmfXZYW (P : FinitePMF (α × β × γ × δ)) :
    FinitePMF (α × γ × (β × δ)) :=
  FinitePMF.comapEquiv equivXZYW P

lemma condMutualInfo_pmfYZXW (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfYZXW P) = I_YZ_XW P := by
  let eXYW : α × β × δ ≃ β × (α × δ) := {
    toFun := fun t => (t.2.1, (t.1, t.2.2))
    invFun := fun t => (t.2.1, t.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨y, x, w⟩; rfl
  }
  let eXZW : α × γ × δ ≃ γ × (α × δ) := {
    toFun := fun t => (t.2.1, (t.1, t.2.2))
    invFun := fun t => (t.2.1, t.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨x, z, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨z, x, w⟩; rfl
  }
  have hXYW : entropyOf (marginalXZMass (pmfYZXW P)) =
      entropyOf (marginalXYWMass P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalXYWMass P)
      (marginalXZMass (pmfYZXW P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hXZW : entropyOf (marginalYZMass (pmfYZXW P)) =
      entropyOf (marginalXZWMass P) := by
    symm
    refine entropyOf_equiv_eq eXZW (marginalXZWMass P)
      (marginalYZMass (pmfYZXW P)) ?_
    intro xzw
    rcases xzw with ⟨x, z, w⟩
    rfl
  have hXW : entropyOf (marginalZMass (pmfYZXW P)) =
      entropyOf (marginalXWMass P) := by
    apply congrArg entropyOf
    funext xw
    rcases xw with ⟨x, w⟩
    rfl
  have hFull : entropyOf (fun yz_xw : β × γ × (α × δ) => (pmfYZXW P).pmf yz_xw) =
      entropyOf P.pmf := by
    symm
    refine entropyOf_equiv_eq equivYZXW.symm
      P.pmf
      (fun yz_xw : β × γ × (α × δ) => (pmfYZXW P).pmf yz_xw) ?_
    intro xyzw
    rcases xyzw with ⟨x, y, z, w⟩
    rfl
  unfold condMutualInfo I_YZ_XW entropy
  rw [hXYW, hXZW, hXW, hFull]

lemma condMutualInfo_pmfXZYW (P : FinitePMF (α × β × γ × δ)) :
    condMutualInfo (pmfXZYW P) = I_XZ_YW P := by
  let eXYW : α × β × δ ≃ α × (β × δ) := {
    toFun := fun t => (t.1, (t.2.1, t.2.2))
    invFun := fun t => (t.1, t.2.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨x, y, w⟩; rfl
  }
  let eYZW : β × γ × δ ≃ γ × (β × δ) := {
    toFun := fun t => (t.2.1, (t.1, t.2.2))
    invFun := fun t => (t.2.1, t.1, t.2.2)
    left_inv := by intro t; rcases t with ⟨y, z, w⟩; rfl
    right_inv := by intro t; rcases t with ⟨z, y, w⟩; rfl
  }
  have hXYW : entropyOf (marginalXZMass (pmfXZYW P)) =
      entropyOf (marginalXYWMass P) := by
    symm
    refine entropyOf_equiv_eq eXYW (marginalXYWMass P)
      (marginalXZMass (pmfXZYW P)) ?_
    intro xyw
    rcases xyw with ⟨x, y, w⟩
    rfl
  have hYZW : entropyOf (marginalYZMass (pmfXZYW P)) =
      entropyOf (marginalYZWMass P) := by
    symm
    refine entropyOf_equiv_eq eYZW (marginalYZWMass P)
      (marginalYZMass (pmfXZYW P)) ?_
    intro yzw
    rcases yzw with ⟨y, z, w⟩
    rfl
  have hYW : entropyOf (marginalZMass (pmfXZYW P)) =
      entropyOf (marginalYWMass P) := by
    apply congrArg entropyOf
    funext yw
    rcases yw with ⟨y, w⟩
    rfl
  have hFull : entropyOf (fun xz_yw : α × γ × (β × δ) => (pmfXZYW P).pmf xz_yw) =
      entropyOf P.pmf := by
    symm
    refine entropyOf_equiv_eq equivXZYW.symm
      P.pmf
      (fun xz_yw : α × γ × (β × δ) => (pmfXZYW P).pmf xz_yw) ?_
    intro xyzw
    rcases xyzw with ⟨x, y, z, w⟩
    rfl
  unfold condMutualInfo I_XZ_YW entropy
  rw [hXYW, hYZW, hYW, hFull]

/-- Conditional Markovity as a concrete equality. -/
def condMarkov (P : FinitePMF (α × β × γ × δ)) : Prop :=
  ∀ x y z w,
    P.pmf (x, y, z, w) * marginalYWMass P (y, w)
      =
    marginalXYWMass P (x, y, w) * marginalYZWMass P (y, z, w)

lemma I_YZ_XW_nonneg (P : FinitePMF (α × β × γ × δ)) : 0 ≤ I_YZ_XW P := by
  have h := condMutualInfo_nonneg (pmfYZXW P)
  rwa [condMutualInfo_pmfYZXW P] at h

lemma I_XZ_YW_eq_zero_of_condMarkov
    (P : FinitePMF (α × β × γ × δ)) (h : condMarkov P) :
    I_XZ_YW P = 0 := by
  have hzero := condMutualInfo_eq_zero_of_condIndep (pmfXZYW P) ?_
  · rwa [condMutualInfo_pmfXZYW P] at hzero
  · intro x z yw
    rcases yw with ⟨y, w⟩
    simpa [condIndep, pmfXZYW, FinitePMF.comapEquiv, equivXZYW, marginalZMass,
      marginalXZMass, marginalYZMass, marginalYWMass, marginalXYWMass,
      marginalYZWMass] using h x y z w

end

end CausalQIF.Probability
