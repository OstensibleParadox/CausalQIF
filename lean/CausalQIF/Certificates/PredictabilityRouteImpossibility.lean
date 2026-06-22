import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace CausalQIF

/-!
# Legacy Predictability-Route Impossibility

This module is retained for off-root compatibility with earlier artifact
imports. It is a surrogate-only route: residual autonomy is represented by
unpredictability above an error threshold, not by `H(I | T) > 0`, and decision
relevance is represented by same-trace covariation, not by conditional mutual
information.

The active paper-facing finite-Shannon theorem is
`CausalQIF.no_entropic_eis_autoregressive` in
`CausalQIF.Certificates.EntropicEIS`.
-/

/-- Minimal normalized, monotone set-function interface used by the legacy surrogate. -/
class ProbSpace (Ω : Type*) where
  prob : Set Ω → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_univ : prob Set.univ = 1
  prob_mono : ∀ {s t : Set Ω}, s ⊆ t → prob s ≤ prob t

/--
Legacy predictability surrogate: `S` is predictable from `T` at error `eps`
when some trace-level predictor has error set bounded by `eps`.
-/
def IsPredictable {Ω State Trace : Type*} [ps : ProbSpace Ω]
    (S : Ω → State) (T : Ω → Trace) (eps : ℝ) : Prop :=
  ∃ hat_S : Trace → State, ps.prob {ω | hat_S (T ω) ≠ S ω} ≤ eps

/--
Legacy EIS witness predicate using predictability and same-trace covariation
surrogates. This is not the paper-facing Shannon witness.
-/
structure IsEISWitness {Ω State Trace Action IState : Type*} [ps : ProbSpace Ω]
    (S : Ω → State) (T : Ω → Trace) (A : Ω → Action)
    (I : Ω → IState) (chi : State → IState) (eps_min : ℝ) : Prop where
  /-- Endogeneity: `I` factors through the full operative state by projection `chi`. -/
  endogeneity : ∀ ω, I ω = chi (S ω)
  /-- Surrogate residual autonomy: `I` is not predictable from `T` below `eps_min`. -/
  residual_autonomy : ¬ IsPredictable I T eps_min
  /-- Surrogate decision relevance: same-trace covariation of `I` and `A`. -/
  decision_relevance : ∃ ω₁ ω₂ : Ω, T ω₁ = T ω₂ ∧ I ω₁ ≠ I ω₂ ∧ A ω₁ ≠ A ω₂

/--
Legacy screenability lemma: predictability of the full state transfers to any
projection of that state.
-/
lemma screenability_lemma_predictability
    {Ω State Trace IState : Type*} [ps : ProbSpace Ω]
    (S : Ω → State) (T : Ω → Trace) (eps : ℝ) (chi : State → IState)
    (hS : IsPredictable S T eps) :
    IsPredictable (fun ω => chi (S ω)) T eps := by
  rcases hS with ⟨hat_S, h_err⟩
  let hat_I : Trace → IState := fun t => chi (hat_S t)
  use hat_I
  have h_subset :
      {ω | hat_I (T ω) ≠ chi (S ω)}
        ⊆ {ω | hat_S (T ω) ≠ S ω} := by
    intro ω h_bad h_good
    exact h_bad (by simp [hat_I, h_good])
  exact le_trans (ps.prob_mono h_subset) h_err

/--
Legacy surrogate theorem. Prefer `no_entropic_eis_autoregressive` for the
paper-facing finite-Shannon statement.
-/
theorem internal_impossibility_predictability
    {Ω State Trace Action IState : Type*} [ps : ProbSpace Ω]
    (S : Ω → State) (T : Ω → Trace) (A : Ω → Action)
    (eps eps_min : ℝ) (h_bound : eps < eps_min)
    (h_screen : IsPredictable S T eps)
    (chi : State → IState) (I : Ω → IState) :
    ¬ IsEISWitness S T A I chi eps_min := by
  intro hEIS
  have h_autonomy := hEIS.residual_autonomy
  have h_I_pred : IsPredictable I T eps := by
    have h_eq : I = (fun ω => chi (S ω)) := funext hEIS.endogeneity
    rw [h_eq]
    exact screenability_lemma_predictability S T eps chi h_screen
  have h_I_pred_min : IsPredictable I T eps_min := by
    rcases h_I_pred with ⟨hat_I, h_err⟩
    use hat_I
    exact le_trans h_err (le_of_lt h_bound)
  exact h_autonomy h_I_pred_min

/-- Readable alias for the legacy predictability-route theorem. -/
theorem internal_route_impossibility_predictability
    {Ω State Trace Action IState : Type*} [ps : ProbSpace Ω]
    (S : Ω → State) (T : Ω → Trace) (A : Ω → Action)
    (eps eps_min : ℝ) (h_bound : eps < eps_min)
    (h_screen : IsPredictable S T eps)
    (chi : State → IState) (I : Ω → IState) :
    ¬ IsEISWitness S T A I chi eps_min :=
  internal_impossibility_predictability S T A eps eps_min h_bound h_screen chi I

end CausalQIF
