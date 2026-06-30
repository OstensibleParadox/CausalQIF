import CausalQIF.InfoTheory

/-!
# Dynamic Probe Certificate Bound

Canonical declarations for dynamic probe certificates.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

noncomputable section

section DynamicCertificate

variable {Probe State Action Trace : Type}
variable [Fintype Probe] [Fintype State] [Fintype Action] [Fintype Trace]
variable [DecidableEq Probe] [DecidableEq State] [DecidableEq Action] [DecidableEq Trace]

/-- True residual decision relevance given the visible trace. -/
def delta_act (P : FinitePMF (Probe × State × Action × Trace)) : ℝ :=
  I_YZ_W P

/--
Proposition 2: Gray-Box-Access Closer (Conditional DPI).
Gap-closer for Theorem~1: if X_t is a probe variable satisfying the conditional
Markov chain X_t → S_t → A_t given T_tilde_t, then its conditional MI with A_t
lower-bounds delta_act, ruling out the P₀ (Dirac) realization.
-/
theorem probe_action_cmi_le_state_action_cmi_of_condMarkov (P : FinitePMF (Probe × State × Action × Trace))
    (h_markov : condMarkov P) :
    I_XZ_W P ≤ delta_act P := by
  exact cond_dpi P h_markov

/--
Lift a joint distribution on `(State, Action, Trace)` with a deterministic probe
readout.  The resulting four-variable PMF has coordinates
`(Probe, State, Action, Trace)`.
-/
def deterministicProbePMF
    (Q : FinitePMF (State × Action × Trace))
    (probe : State → Trace → Probe) :
    FinitePMF (Probe × State × Action × Trace) :=
  FinitePMF.map Q fun sat => (probe sat.1 sat.2.2, sat.1, sat.2.1, sat.2.2)

lemma deterministicProbePMF_apply
    (Q : FinitePMF (State × Action × Trace))
    (probe : State → Trace → Probe)
    (x : Probe) (y : State) (z : Action) (w : Trace) :
    (deterministicProbePMF Q probe).pmf (x, y, z, w) =
      if probe y w = x then Q.pmf (y, z, w) else 0 := by
  unfold deterministicProbePMF FinitePMF.map
  change
    (∑ sat : State × Action × Trace,
      if (probe sat.1 sat.2.2, sat.1, sat.2.1, sat.2.2) = (x, y, z, w)
      then Q.pmf sat else 0)
      =
        if probe y w = x then Q.pmf (y, z, w) else 0
  by_cases hprobe : probe y w = x
  · rw [if_pos hprobe]
    rw [Finset.sum_eq_single (y, z, w)]
    · simp [hprobe]
    · intro sat _ hsat
      simp only [ite_eq_right_iff]
      intro htuple
      exfalso
      apply hsat
      rcases Prod.ext_iff.mp htuple with ⟨_, hrest₁⟩
      rcases Prod.ext_iff.mp hrest₁ with ⟨hy, hrest₂⟩
      rcases Prod.ext_iff.mp hrest₂ with ⟨hz, hw⟩
      ext
      · exact hy
      · exact hz
      · exact hw
    · intro hmem
      simp at hmem
  · rw [if_neg hprobe]
    apply Finset.sum_eq_zero
    intro sat _
    rcases sat with ⟨sat_y, sat_z, sat_w⟩
    simp only [ite_eq_right_iff]
    intro htuple
    exfalso
    apply hprobe
    rcases Prod.ext_iff.mp htuple with ⟨hx, hrest₁⟩
    rcases Prod.ext_iff.mp hrest₁ with ⟨hy, hrest₂⟩
    rcases Prod.ext_iff.mp hrest₂ with ⟨_, hw⟩
    subst hy
    subst hw
    exact hx

lemma marginalYWMass_deterministicProbePMF
    (Q : FinitePMF (State × Action × Trace))
    (probe : State → Trace → Probe)
    (y : State) (w : Trace) :
    marginalYWMass (deterministicProbePMF Q probe) (y, w) =
      ∑ z : Action, Q.pmf (y, z, w) := by
  unfold marginalYWMass
  calc
    ∑ x : Probe, ∑ z : Action,
        (deterministicProbePMF Q probe).pmf (x, y, z, w)
        =
      ∑ x : Probe, ∑ z : Action,
        if probe y w = x then Q.pmf (y, z, w) else 0 := by
          simp [deterministicProbePMF_apply]
    _ =
      ∑ z : Action, ∑ x : Probe,
        if probe y w = x then Q.pmf (y, z, w) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ z : Action, Q.pmf (y, z, w) := by
          simp

lemma marginalXYWMass_deterministicProbePMF
    (Q : FinitePMF (State × Action × Trace))
    (probe : State → Trace → Probe)
    (x : Probe) (y : State) (w : Trace) :
    marginalXYWMass (deterministicProbePMF Q probe) (x, y, w) =
      if probe y w = x then ∑ z : Action, Q.pmf (y, z, w) else 0 := by
  unfold marginalXYWMass
  calc
    ∑ z : Action, (deterministicProbePMF Q probe).pmf (x, y, z, w)
        = ∑ z : Action, if probe y w = x then Q.pmf (y, z, w) else 0 := by
          simp [deterministicProbePMF_apply]
    _ = if probe y w = x then ∑ z : Action, Q.pmf (y, z, w) else 0 := by
          by_cases hprobe : probe y w = x <;> simp [hprobe]

lemma marginalYZWMass_deterministicProbePMF
    (Q : FinitePMF (State × Action × Trace))
    (probe : State → Trace → Probe)
    (y : State) (z : Action) (w : Trace) :
    marginalYZWMass (deterministicProbePMF Q probe) (y, z, w) =
      Q.pmf (y, z, w) := by
  unfold marginalYZWMass
  calc
    ∑ x : Probe, (deterministicProbePMF Q probe).pmf (x, y, z, w)
        = ∑ x : Probe, if probe y w = x then Q.pmf (y, z, w) else 0 := by
          simp [deterministicProbePMF_apply]
    _ = Q.pmf (y, z, w) := by
          simp

/--
Deterministic probe readouts satisfy the conditional Markov premise required by
conditional DPI.  Thus the dynamic lower-bound theorem does not need an
external `condMarkov` hypothesis for probes constructed from `(State, Trace)`.
-/
theorem condMarkov_deterministicProbePMF
    (Q : FinitePMF (State × Action × Trace))
    (probe : State → Trace → Probe) :
    condMarkov (deterministicProbePMF Q probe) := by
  intro x y z w
  rw [deterministicProbePMF_apply,
    marginalYWMass_deterministicProbePMF,
    marginalXYWMass_deterministicProbePMF,
    marginalYZWMass_deterministicProbePMF]
  by_cases hprobe : probe y w = x <;> simp [hprobe, mul_comm]

/--
Dynamic lower bound with the Markov premise discharged by construction.
For a deterministic probe readout of `(State, Trace)`, the certified probe
information lower-bounds residual decision relevance.
-/
theorem probe_action_cmi_le_state_action_cmi_of_deterministicProbe
    (Q : FinitePMF (State × Action × Trace))
    (probe : State → Trace → Probe) :
    I_XZ_W (deterministicProbePMF Q probe) ≤
      delta_act (deterministicProbePMF Q probe) :=
  probe_action_cmi_le_state_action_cmi_of_condMarkov (deterministicProbePMF Q probe)
    (condMarkov_deterministicProbePMF Q probe)

/--
Aggregated Dynamic Certificate.
Taking the maximum of several valid probe classes (e.g., replay, intervention, proxy)
yields a valid lower bound.
-/
theorem max_probe_action_cmi_le_state_action_cmi_of_markov_probes
    (P_replay : FinitePMF (Probe × State × Action × Trace))
    (P_interv : FinitePMF (Probe × State × Action × Trace))
    (P_proxy : FinitePMF (Probe × State × Action × Trace))
    (h1 : condMarkov P_replay)
    (h2 : condMarkov P_interv)
    (h3 : condMarkov P_proxy) :
    max (I_XZ_W P_replay)
        (max (I_XZ_W P_interv) (I_XZ_W P_proxy)) ≤
    max (delta_act P_replay)
        (max (delta_act P_interv) (delta_act P_proxy)) := by
  have hb1 := probe_action_cmi_le_state_action_cmi_of_condMarkov P_replay h1
  have hb2 := probe_action_cmi_le_state_action_cmi_of_condMarkov P_interv h2
  have hb3 := probe_action_cmi_le_state_action_cmi_of_condMarkov P_proxy h3
  apply max_le
  · exact hb1.trans (le_max_left _ _)
  · apply max_le
    · exact hb2.trans (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact hb3.trans (le_trans (le_max_right _ _) (le_max_right _ _))

/--
Aggregated Dynamic Certificate for Deterministic Probes.
For a set of deterministic probe readouts of `(State, Trace)`, the aggregated certified probe
information lower-bounds the aggregated residual decision relevance, without needing
external `condMarkov` hypotheses.
-/
theorem max_probe_action_cmi_of_deterministic_probes
    (Q : FinitePMF (State × Action × Trace))
    (probe_replay : State → Trace → Probe)
    (probe_interv : State → Trace → Probe)
    (probe_proxy : State → Trace → Probe) :
    max (I_XZ_W (deterministicProbePMF Q probe_replay))
        (max (I_XZ_W (deterministicProbePMF Q probe_interv))
             (I_XZ_W (deterministicProbePMF Q probe_proxy))) ≤
    max (delta_act (deterministicProbePMF Q probe_replay))
        (max (delta_act (deterministicProbePMF Q probe_interv))
             (delta_act (deterministicProbePMF Q probe_proxy))) :=
  max_probe_action_cmi_le_state_action_cmi_of_markov_probes
    (deterministicProbePMF Q probe_replay)
    (deterministicProbePMF Q probe_interv)
    (deterministicProbePMF Q probe_proxy)
    (condMarkov_deterministicProbePMF Q probe_replay)
    (condMarkov_deterministicProbePMF Q probe_interv)
    (condMarkov_deterministicProbePMF Q probe_proxy)

end DynamicCertificate

end

namespace Certificates

export CausalQIF (
  probe_action_cmi_le_state_action_cmi_of_condMarkov
  probe_action_cmi_le_state_action_cmi_of_deterministicProbe
  max_probe_action_cmi_le_state_action_cmi_of_markov_probes
  max_probe_action_cmi_of_deterministic_probes
  delta_act
)

end Certificates

end CausalQIF
