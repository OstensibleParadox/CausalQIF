import CausalQIF.Certificates.DynamicProbeBound
import CausalQIF.Certificates.StaticCutBound
import CausalQIF.Certificates.AdditiveCutBound

/--!
Compatibility layer for legacy theorem names.

This module now only keeps deprecated aliases to preserve API stability while
moving canonical declarations to the modular `*Bound` modules.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

@[deprecated probe_action_cmi_le_state_action_cmi_of_condMarkov (since := "2026-06-30")] 
alias prop2_dynamic_lb := probe_action_cmi_le_state_action_cmi_of_condMarkov

@[deprecated probe_action_cmi_le_state_action_cmi_of_deterministicProbe (since := "2026-06-30")] 
alias prop2_dynamic_lb_deterministic_probe := probe_action_cmi_le_state_action_cmi_of_deterministicProbe

@[deprecated max_probe_action_cmi_le_state_action_cmi_of_markov_probes (since := "2026-06-30")] 
alias aggregated_dynamic_lb := max_probe_action_cmi_le_state_action_cmi_of_markov_probes

@[deprecated max_probe_action_cmi_of_deterministic_probes (since := "2026-06-30")] 
alias aggregated_dynamic_lb_deterministic_probes := max_probe_action_cmi_of_deterministic_probes

@[deprecated hidden_trace_entropy_le_cut_capacity (since := "2026-06-30")] 
alias prop1_static_ub := hidden_trace_entropy_le_cut_capacity

@[deprecated hidden_trace_entropy_le_entropic_cap (since := "2026-06-30")] 
alias prop1_static_ub_bounded := hidden_trace_entropy_le_entropic_cap

@[deprecated hidden_trace_entropy_le_sum_cut_capacities (since := "2026-06-30")] 
alias corollary_additive_ub := hidden_trace_entropy_le_sum_cut_capacities

end CausalQIF
