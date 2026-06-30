import CausalQIF.Paper.POPL2027
import CausalQIF.Paper.Compatibility

/-
# Paper-Theorem Aggregates

Canonical paper-facing theorem entrypoint for `import CausalQIF.Paper.MainTheorems`.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF.Paper

namespace MainTheorems

export CausalQIF.Paper (theorem1_identifiability_gap proposition2_dynamic_lower_bound
  proposition2_dynamic_lower_bound_deterministic proposition1_static_entropic_cut_bound
  theorem2_linear_chain_cut_set theorem3_pac_lower_bound theorem2a_bridge)

export CausalQIF.Paper.Compatibility (dSeparation_implies_conditional_independence)

end MainTheorems

end CausalQIF.Paper
