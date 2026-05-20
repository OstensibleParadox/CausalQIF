import CausalQIF.Probability.FinitePMF.Basic

open Finset
open scoped BigOperators Real

namespace CausalQIF.Probability

noncomputable section

/-! # Two- and Three-Variable Marginals

Position-indexed marginals of `FinitePMF`. For 2-tuples: `marginalPair_Fst`,
`marginalPair_Snd`, and the general 2→1 transporter `marginalizeLeafPMF`.
For 3-tuples: `marginalTriple_Thd`, `marginalTriple_FstThd`,
`marginalTriple_SndThd`, plus their non-negativity, summation, and pullback
identities.
-/

variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Pair marginals -/

def marginalPair_Fst (P : FinitePMF (α × β)) (x : α) : ℝ :=
  ∑ y : β, P.pmf (x, y)

def marginalPair_Snd (P : FinitePMF (α × β)) (y : β) : ℝ :=
  ∑ x : α, P.pmf (x, y)

lemma marginalPair_Fst_nonneg (P : FinitePMF (α × β)) (x : α) :
    0 ≤ marginalPair_Fst P x :=
  Finset.sum_nonneg (fun y _ => P.pmf_nonneg (x, y))

lemma marginalPair_Snd_nonneg (P : FinitePMF (α × β)) (y : β) :
    0 ≤ marginalPair_Snd P y :=
  Finset.sum_nonneg (fun x _ => P.pmf_nonneg (x, y))

lemma marginalPair_Fst_sum_one (P : FinitePMF (α × β)) :
    ∑ x : α, marginalPair_Fst P x = 1 := by
  unfold marginalPair_Fst
  rw [← Finset.sum_product]
  exact P.sum_one

lemma marginalPair_Snd_sum_one (P : FinitePMF (α × β)) :
    ∑ y : β, marginalPair_Snd P y = 1 := by
  unfold marginalPair_Snd
  rw [Finset.sum_comm]
  rw [← Finset.sum_product]
  exact P.sum_one

def marginalizeLeafPMF (P : FinitePMF (α × β)) : FinitePMF α where
  pmf x := ∑ leaf : β, P.pmf (x, leaf)
  pmf_nonneg x := by
    exact Finset.sum_nonneg fun leaf _ => P.pmf_nonneg (x, leaf)
  sum_one := by
    calc
      ∑ x : α, ∑ leaf : β, P.pmf (x, leaf)
          = ∑ p : α × β, P.pmf p := (Finset.sum_product (f := P.pmf) (s := univ) (t := univ)).symm
      _ = 1 := P.sum_one

/-! ## Three-variable marginals -/

def marginalTriple_Thd (P : FinitePMF (α × β × γ)) (z : γ) : ℝ :=
  ∑ x : α, ∑ y : β, P.pmf (x, y, z)

def marginalTriple_FstThd (P : FinitePMF (α × β × γ)) (xz : α × γ) : ℝ :=
  ∑ y : β, P.pmf (xz.1, y, xz.2)

def marginalTriple_SndThd (P : FinitePMF (α × β × γ)) (yz : β × γ) : ℝ :=
  ∑ x : α, P.pmf (x, yz.1, yz.2)

lemma marginalTriple_FstThd_nonneg (P : FinitePMF (α × β × γ)) (xz : α × γ) :
    0 ≤ marginalTriple_FstThd P xz :=
  Finset.sum_nonneg (fun y _ => P.pmf_nonneg (xz.1, y, xz.2))

lemma marginalTriple_SndThd_nonneg (P : FinitePMF (α × β × γ)) (yz : β × γ) :
    0 ≤ marginalTriple_SndThd P yz :=
  Finset.sum_nonneg (fun x _ => P.pmf_nonneg (x, yz.1, yz.2))

lemma marginalTriple_Thd_nonneg (P : FinitePMF (α × β × γ)) (z : γ) :
    0 ≤ marginalTriple_Thd P z :=
  Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => P.pmf_nonneg (x, y, z)))

lemma marginalTriple_FstThd_sum_thd (P : FinitePMF (α × β × γ)) (z : γ) :
    ∑ x : α, marginalTriple_FstThd P (x, z) = marginalTriple_Thd P z := by
  rfl

lemma marginalTriple_SndThd_sum_thd (P : FinitePMF (α × β × γ)) (z : γ) :
    ∑ y : β, marginalTriple_SndThd P (y, z) = marginalTriple_Thd P z := by
  unfold marginalTriple_SndThd marginalTriple_Thd
  rw [Finset.sum_comm]

lemma marginalTriple_Thd_sum_one (P : FinitePMF (α × β × γ)) :
    ∑ z : γ, marginalTriple_Thd P z = 1 := by
  have hsum : (∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z)) = 1 := by
    calc
      (∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z))
          = ∑ x : α, ∑ yz : β × γ, P.pmf (x, yz.1, yz.2) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [← Fintype.sum_prod_type' (fun y z => P.pmf (x, y, z))]
      _ = ∑ xyz : α × β × γ, P.pmf xyz := by
            rw [← Fintype.sum_prod_type]
      _ = 1 := P.sum_one
  unfold marginalTriple_Thd
  rw [Finset.sum_comm]
  rw [show (∑ x : α, ∑ z : γ, ∑ y : β, P.pmf (x, y, z))
      = ∑ x : α, ∑ y : β, ∑ z : γ, P.pmf (x, y, z) by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]]
  exact hsum

/-! ## Pullback Lemmas -/

lemma marginalTriple_FstThd_pullback (P : FinitePMF (α × β × γ)) (f : α × γ → ℝ) :
    ∑ xz : α × γ, marginalTriple_FstThd P xz * f xz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (a, c) := by
  unfold marginalTriple_FstThd
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

lemma marginalTriple_SndThd_pullback (P : FinitePMF (α × β × γ)) (f : β × γ → ℝ) :
    ∑ yz : β × γ, marginalTriple_SndThd P yz * f yz =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f (b, c) := by
  unfold marginalTriple_SndThd
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

lemma marginalTriple_Thd_pullback (P : FinitePMF (α × β × γ)) (f : γ → ℝ) :
    ∑ z : γ, marginalTriple_Thd P z * f z =
    ∑ a : α, ∑ b : β, ∑ c : γ, P.pmf (a, b, c) * f c := by
  unfold marginalTriple_Thd
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
