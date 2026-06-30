import CausalQIF.Certificates.DualCertificate

/-
# Static Cut-Bound Certificates

Canonical re-export for static structural entropy bounds and cut-capacity budget
lemmas.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

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
