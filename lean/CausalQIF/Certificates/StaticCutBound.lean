import CausalQIF.InfoTheory

/-!
# Static Cut-Bound Certificates

Canonical declarations for static structural entropy bounds and cut-capacity budget
lemmas.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

noncomputable section

section StaticCertificate

variable {State VisibleTrace MissingTrace : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace]

def stateVisibleMass (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (st : State × VisibleTrace) : ℝ :=
  ∑ m : MissingTrace, P.pmf (st.1, st.2, m)

def visibleMass (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (t : VisibleTrace) : ℝ :=
  ∑ s : State, ∑ m : MissingTrace, P.pmf (s, t, m)

def visibleMissingMass (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (tm : VisibleTrace × MissingTrace) : ℝ :=
  ∑ s : State, P.pmf (s, tm.1, tm.2)

lemma visibleMass_nonneg (P : FinitePMF (State × VisibleTrace × MissingTrace)) (t : VisibleTrace) :
    0 ≤ visibleMass P t := by
  unfold visibleMass
  exact Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun m _ => P.pmf_nonneg (s, t, m)))

lemma visibleMissingMass_nonneg (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (tm : VisibleTrace × MissingTrace) :
    0 ≤ visibleMissingMass P tm := by
  unfold visibleMissingMass
  exact Finset.sum_nonneg (fun s _ => P.pmf_nonneg (s, tm.1, tm.2))

lemma visibleMissingMass_sum_one (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    ∑ tm : VisibleTrace × MissingTrace, visibleMissingMass P tm = 1 := by
  unfold visibleMissingMass
  calc
    ∑ tm : VisibleTrace × MissingTrace, ∑ s : State, P.pmf (s, tm.1, tm.2)
        = ∑ t : VisibleTrace, ∑ m : MissingTrace, ∑ s : State, P.pmf (s, t, m) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ t : VisibleTrace, ∑ s : State, ∑ m : MissingTrace, P.pmf (s, t, m) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.sum_comm]
    _ = ∑ s : State, ∑ t : VisibleTrace, ∑ m : MissingTrace, P.pmf (s, t, m) := by
          rw [Finset.sum_comm]
    _ = ∑ s : State, ∑ tm : VisibleTrace × MissingTrace, P.pmf (s, tm.1, tm.2) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [← Fintype.sum_prod_type' (fun t m => P.pmf (s, t, m))]
    _ = ∑ stm : State × VisibleTrace × MissingTrace, P.pmf stm := by
          rw [← Fintype.sum_prod_type]
    _ = 1 := P.sum_one

def fullTraceEntropy (P : FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  entropyOf (fun stm : State × VisibleTrace × MissingTrace => P.pmf stm)

/-- `H(S | T_tilde)`. -/
def H_S_cond_Ttilde (P : FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  entropyOf (stateVisibleMass P) - entropyOf (visibleMass P)

/-- `H(S | T_full)`, where `T_full = (T_tilde, M)`. -/
def H_S_cond_Tfull (P : FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  fullTraceEntropy P - entropyOf (visibleMissingMass P)

/-- `I(S; M | T_tilde)`. -/
def I_S_M_cond_Ttilde (P : FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  entropyOf (stateVisibleMass P) +
    entropyOf (visibleMissingMass P) -
    entropyOf (visibleMass P) -
    fullTraceEntropy P

/-- Static algebraic decomposition for the visible/full trace entropy gap. -/
theorem static_decomposition (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    H_S_cond_Ttilde P = H_S_cond_Tfull P + I_S_M_cond_Ttilde P := by
  unfold H_S_cond_Ttilde H_S_cond_Tfull I_S_M_cond_Ttilde fullTraceEntropy
  ring

/-- Marginal of the missing trace M. -/
def missingMass (P : FinitePMF (State × VisibleTrace × MissingTrace)) (m : MissingTrace) : ℝ :=
  ∑ s : State, ∑ t : VisibleTrace, P.pmf (s, t, m)

lemma missingMass_nonneg (P : FinitePMF (State × VisibleTrace × MissingTrace)) (m : MissingTrace) :
    0 ≤ missingMass P m :=
  Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun t _ => P.pmf_nonneg (s, t, m)))

lemma missingMass_sum_one (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    ∑ m : MissingTrace, missingMass P m = 1 := by
  unfold missingMass
  calc
    ∑ m : MissingTrace, ∑ s : State, ∑ t : VisibleTrace, P.pmf (s, t, m)
        = ∑ s : State, ∑ t : VisibleTrace, ∑ m : MissingTrace, P.pmf (s, t, m) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
    _ = ∑ s : State, ∑ tm : VisibleTrace × MissingTrace, P.pmf (s, tm.1, tm.2) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [← Fintype.sum_prod_type' (fun t m => P.pmf (s, t, m))]
    _ = ∑ stm : State × VisibleTrace × MissingTrace, P.pmf stm := by
          rw [← Fintype.sum_prod_type]
    _ = 1 := P.sum_one

/-- Entropy of the missing trace. -/
def H_M (P : FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  entropyOf (missingMass P)

lemma condEntropy_M_cond_Ttilde_le_H_M (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    entropyOf (visibleMissingMass P) - entropyOf (visibleMass P) ≤ H_M P := by
  let Q : FinitePMF (MissingTrace × VisibleTrace) := {
    pmf := fun mt => visibleMissingMass P (mt.2, mt.1)
    pmf_nonneg := by
      intro mt
      exact visibleMissingMass_nonneg P (mt.2, mt.1)
    sum_one := by
      have h := visibleMissingMass_sum_one P
      calc
        ∑ mt : MissingTrace × VisibleTrace, visibleMissingMass P (mt.2, mt.1)
            = ∑ tm : VisibleTrace × MissingTrace, visibleMissingMass P tm := by
              let e : MissingTrace × VisibleTrace ≃ VisibleTrace × MissingTrace := {
                toFun := fun mt => (mt.2, mt.1)
                invFun := fun tm => (tm.2, tm.1)
                left_inv := by intro mt; rcases mt with ⟨m, t⟩; rfl
                right_inv := by intro tm; rcases tm with ⟨t, m⟩; rfl
              }
              exact Equiv.sum_comp e (visibleMissingMass P)
        _ = 1 := h
  }
  have hmi := mutualInfo_nonneg Q
  have hleft : entropyOf (marginalPairFst Q) = H_M P := by
    unfold H_M marginalPairFst missingMass Q visibleMissingMass
    apply congrArg entropyOf
    funext m
    rw [Finset.sum_comm]
  have hright : entropyOf (marginalPairSnd Q) = entropyOf (visibleMass P) := by
    unfold marginalPairSnd visibleMass Q visibleMissingMass
    apply congrArg entropyOf
    funext t
    rw [Finset.sum_comm]
  have hjoint : entropyOf Q.pmf = entropyOf (visibleMissingMass P) := by
    let e : MissingTrace × VisibleTrace ≃ VisibleTrace × MissingTrace := {
      toFun := fun mt => (mt.2, mt.1)
      invFun := fun tm => (tm.2, tm.1)
      left_inv := by intro mt; rcases mt with ⟨m, t⟩; rfl
      right_inv := by intro tm; rcases tm with ⟨t, m⟩; rfl
    }
    refine entropyOf_equiv_eq e (fun mt : MissingTrace × VisibleTrace => Q.pmf mt)
      (visibleMissingMass P) ?_
    intro mt
    rfl
  unfold mutualInfo at hmi
  rw [hleft, hright, hjoint] at hmi
  linarith

lemma I_S_M_cond_Ttilde_le_condEntropy_M_cond_Ttilde
    (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    I_S_M_cond_Ttilde P ≤ entropyOf (visibleMissingMass P) - entropyOf (visibleMass P) := by
  let Q : FinitePMF (MissingTrace × (State × VisibleTrace)) := {
    pmf := fun mst => P.pmf (mst.2.1, mst.2.2, mst.1)
    pmf_nonneg := by
      intro mst
      exact P.pmf_nonneg (mst.2.1, mst.2.2, mst.1)
    sum_one := by
      calc
        ∑ mst : MissingTrace × (State × VisibleTrace), P.pmf (mst.2.1, mst.2.2, mst.1)
            = ∑ m : MissingTrace, ∑ st : State × VisibleTrace, P.pmf (st.1, st.2, m) := by
              rw [Fintype.sum_prod_type]
        _ = ∑ m : MissingTrace, ∑ s : State, ∑ t : VisibleTrace, P.pmf (s, t, m) := by
              apply Finset.sum_congr rfl
              intro m _
              rw [Fintype.sum_prod_type]
        _ = ∑ m : MissingTrace, missingMass P m := by
              rfl
        _ = 1 := missingMass_sum_one P
  }
  have hcond := condEntropy_nonneg Q
  have hfull : entropyOf Q.pmf = fullTraceEntropy P := by
    unfold fullTraceEntropy Q
    let e : MissingTrace × (State × VisibleTrace) ≃ State × VisibleTrace × MissingTrace := {
      toFun := fun mst => (mst.2.1, mst.2.2, mst.1)
      invFun := fun stm => (stm.2.2, (stm.1, stm.2.1))
      left_inv := by intro mst; rcases mst with ⟨m, s, t⟩; rfl
      right_inv := by intro stm; rcases stm with ⟨s, t, m⟩; rfl
    }
    refine entropyOf_equiv_eq e
      (fun mst : MissingTrace × (State × VisibleTrace) => P.pmf (mst.2.1, mst.2.2, mst.1))
      (fun stm : State × VisibleTrace × MissingTrace => P.pmf stm) ?_
    intro mst
    rfl
  have hmarg : entropyOf (marginalPairSnd Q) = entropyOf (stateVisibleMass P) := by
    unfold marginalPairSnd stateVisibleMass Q
    rfl
  unfold condEntropy at hcond
  rw [hfull, hmarg] at hcond
  unfold I_S_M_cond_Ttilde fullTraceEntropy at *
  linarith

lemma I_S_M_cond_Ttilde_le_H_M (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    I_S_M_cond_Ttilde P ≤ H_M P := by
  exact le_trans (I_S_M_cond_Ttilde_le_condEntropy_M_cond_Ttilde P)
    (condEntropy_M_cond_Ttilde_le_H_M P)

lemma H_M_le_log_card_M
    (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    H_M P ≤ Real.log (Fintype.card MissingTrace : ℝ) / Real.log 2 := by
  let Q : FinitePMF MissingTrace := {
    pmf := missingMass P,
    pmf_nonneg := missingMass_nonneg P,
    sum_one := missingMass_sum_one P
  }
  exact entropy_le_log_card Q

/-- Auxiliary cardinality corollary: the static state-entropy gap is bounded by
    the entropy, hence log-cardinality, of the missing trace. This does not replace
    the cut-set premise in `hidden_trace_entropy_le_cut_capacity`; it is a coarse finite-support bound. -/
theorem hidden_trace_entropy_le_entropic_cap
    (P : FinitePMF (State × VisibleTrace × MissingTrace)) :
    H_S_cond_Ttilde P ≤ H_S_cond_Tfull P + (Real.log (Fintype.card MissingTrace : ℝ) / Real.log 2) := by
  have h_chain := static_decomposition P
  rw [h_chain]
  have h_I_le_H := I_S_M_cond_Ttilde_le_H_M P
  have h_H_le_log := H_M_le_log_card_M P
  have h_total := le_trans h_I_le_H h_H_le_log
  exact add_le_add (le_refl (H_S_cond_Tfull P)) h_total

/--
Software Orthogonality Hypothesis.
Assumes cut capacity is bounded by the sum of edge capacities.
Formulated as a predicate to keep the trusted external premise explicit.
-/
def software_orthogonal (Cut : Type) (C_cut : Cut → ℝ) (C_edge_sum : Cut → ℝ) (Cuts_U_to_S : Set Cut) : Prop :=
    ∀ Ω ∈ Cuts_U_to_S, C_cut Ω ≤ C_edge_sum Ω

/--
Proposition 1: Structural-Access Closer (Static Cut-Sum Bound).
Gap-closer for Theorem~1: under structural access with full logging,
ε_state^UB = 0 collapses both realizations to a single equivalence class.

The premise `h_bound` is the explicit external cut-set/information-flow
assumption for this structural reduction.
-/
theorem hidden_trace_entropy_le_cut_capacity
    (Cut : Type) (C_cut : Cut → ℝ)
    (Ω : Cut)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (h_bound : I_S_M_cond_Ttilde P ≤ C_cut Ω) :
    H_S_cond_Ttilde P ≤ H_S_cond_Tfull P + C_cut Ω := by
  have h_chain := static_decomposition P
  rw [h_chain]
  exact add_le_add (le_refl (H_S_cond_Tfull P)) h_bound

end StaticCertificate

end

namespace Certificates

export CausalQIF (
  hidden_trace_entropy_le_cut_capacity
  hidden_trace_entropy_le_entropic_cap
  H_S_cond_Ttilde
  H_S_cond_Tfull
  I_S_M_cond_Ttilde
  software_orthogonal
)

end Certificates

end CausalQIF
