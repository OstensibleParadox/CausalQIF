import CausalQIF.Certificates.IdentifiabilityGap
import CausalQIF.Certificates.DynamicProbeBound
import CausalQIF.Certificates.StaticCutBound
import CausalQIF.Certificates.PACLowerBound
import CausalQIF.Examples.LinearChain
import CausalQIF.Graph.MarkovBridge

/-!
# POPL 2027 Paper View

Paper-facing theorem names for POPL-oriented statements.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF.Paper

/-! Theorem 1. -/
alias theorem1_identifiability_gap :=
  exists_same_observable_with_cmi_eq_zero_and_cmi_eq_entropy

/-! Proposition 2 (dynamic bound). -/
alias proposition2_dynamic_lower_bound :=
  probe_action_cmi_le_state_action_cmi_of_condMarkov

/-! Proposition 2 (deterministic probe form). -/
alias proposition2_dynamic_lower_bound_deterministic :=
  probe_action_cmi_le_state_action_cmi_of_deterministicProbe

/-! Proposition 1 static entropy gap bound (entropic-capacity form). -/
alias proposition1_static_entropic_cut_bound :=
  hidden_trace_entropy_le_entropic_cap

/-! Case-study one-bit cut-set bound from DAG assumptions. -/
alias theorem2_linear_chain_cut_set :=
  linear_chain_cut_set_bound_of_dSeparated

/-! PAC Theorem 3. -/
alias theorem3_pac_lower_bound :=
  pac_lower_bound_from_conditional_terms

/-! Typed d-separation to conditional-independence bridge used in the paper narrative. -/
alias theorem2a_bridge :=
  CausalQIF.Graph.dSeparation_implies_conditional_independence

end CausalQIF.Paper
