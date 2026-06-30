import CausalQIF.Certificates.StaticCutBound

/-!
# Additive Cut-Bound Certificates

Canonical declarations for additive cut-form entropy decomposition.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

noncomputable section

section AdditiveCutCertificate

variable {State VisibleTrace MissingTrace : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace]

/-- Edge-additive form (Corollary) -/
theorem hidden_trace_entropy_le_sum_cut_capacities
    (Cut : Type) (C_cut : Cut → ℝ) (C_edge_sum : Cut → ℝ) (Cuts_U_to_S : Set Cut)
    (Ω : Cut) (hΩ : Ω ∈ Cuts_U_to_S)
    (P : FinitePMF (State × VisibleTrace × MissingTrace))
    (h_bound : I_S_M_cond_Ttilde P ≤ C_cut Ω)
    (h_ortho : software_orthogonal Cut C_cut C_edge_sum Cuts_U_to_S) :
    H_S_cond_Ttilde P ≤ H_S_cond_Tfull P + C_edge_sum Ω := by
  have h_prop1 := hidden_trace_entropy_le_cut_capacity Cut C_cut Ω P h_bound
  have h_ortho_bound : C_cut Ω ≤ C_edge_sum Ω := h_ortho Ω hΩ
  calc
    H_S_cond_Ttilde P ≤ H_S_cond_Tfull P + C_cut Ω := h_prop1
    _ ≤ H_S_cond_Tfull P + C_edge_sum Ω := add_le_add (le_refl (H_S_cond_Tfull P)) h_ortho_bound

end AdditiveCutCertificate

end

namespace Certificates

export CausalQIF (
  hidden_trace_entropy_le_sum_cut_capacities
)

end Certificates

end CausalQIF
