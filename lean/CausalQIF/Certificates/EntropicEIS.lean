import CausalQIF.InfoTheory.Conditional
import CausalQIF.Certificates.Screenability

namespace CausalQIF

noncomputable section

variable {Ω Trace Action IState : Type}
variable [Fintype Ω] [DecidableEq Ω]
variable [Fintype Trace] [DecidableEq Trace]
variable [Fintype Action] [DecidableEq Action]
variable [Fintype IState] [DecidableEq IState]

/-- Conditional entropy of an observable `X` given trace `T` under a finite outcome PMF. -/
def HcondOf (P : FinitePMF Ω) (X : Ω → IState) (T : Ω → Trace) : ℝ :=
  condEntropy (P.map fun ω => (X ω, T ω))

/-- Conditional mutual information `I(X; A | T)` under a finite outcome PMF. -/
def CMIOf (P : FinitePMF Ω) (X : Ω → IState) (A : Ω → Action) (T : Ω → Trace) : ℝ :=
  condMutualInfo (P.map fun ω => (X ω, A ω, T ω))

variable {State : Type}

/--
Finite-Shannon EIS witness.

This is the paper-facing finite exact form: endogeneity is definitional,
residual autonomy is positive conditional entropy, and decision relevance is
positive conditional mutual information.
-/
structure EntropicEISWitness
    (P : FinitePMF Ω) (S : Ω → State) (T : Ω → Trace) (A : Ω → Action)
    (I : Ω → IState) (chi : State → IState) : Prop where
  /-- Endogeneity: `I` factors through the full operative state by projection `chi`. -/
  endogeneity : ∀ ω, I ω = chi (S ω)
  /-- Residual autonomy: `I` retains positive conditional entropy beyond the trace. -/
  residual_autonomy : 0 < HcondOf P I T
  /-- Decision relevance: `I` carries positive action information beyond the trace. -/
  decision_relevance : 0 < CMIOf P I A T

/--
Under deterministic screenability and endogeneity, the pushed-forward
distribution of `(I, T)` is functionally determined by `T`.
-/
theorem mapped_I_determined_by_T_of_screen
    (P : FinitePMF Ω)
    (screen : DeterministicScreen State Trace)
    (S : Ω → State) (T : Ω → Trace)
    (h_screen : ∀ ω, S ω = screen.recon (T ω))
    (chi : State → IState) (I : Ω → IState)
    (h_endog : ∀ ω, I ω = chi (S ω)) :
    FunctionallyDetermined (P.map fun ω => (I ω, T ω))
      (fun t => chi (screen.recon t)) := by
  intro i t hi
  dsimp [FinitePMF.map]
  apply Finset.sum_eq_zero
  intro ω _
  have hpair_ne : (I ω, T ω) ≠ (i, t) := by
    intro hpair
    have hI : I ω = i := congrArg Prod.fst hpair
    have hT : T ω = t := congrArg Prod.snd hpair
    have hI_recon : I ω = chi (screen.recon t) := by
      calc
        I ω = chi (S ω) := h_endog ω
        _ = chi (screen.recon (T ω)) := by rw [h_screen ω]
        _ = chi (screen.recon t) := by rw [hT]
    exact hi (hI.symm.trans hI_recon)
  simp [hpair_ne]

/--
Paper-facing entropic autoregressive impossibility.

If the operative state is deterministically recoverable from the trace, then
no endogenous internal-state candidate can satisfy positive residual autonomy
`0 < H(I | T)`. The decision-relevance field is part of the witness definition
but is not needed for the contradiction.
-/
theorem no_entropic_eis_autoregressive
    (P : FinitePMF Ω)
    (screen : DeterministicScreen State Trace)
    (S : Ω → State) (T : Ω → Trace) (A : Ω → Action)
    (h_screen : ∀ ω, S ω = screen.recon (T ω))
    (chi : State → IState) (I : Ω → IState) :
    ¬ EntropicEISWitness P S T A I chi := by
  intro hEIS
  have hdet :
      FunctionallyDetermined (P.map fun ω => (I ω, T ω))
        (fun t => chi (screen.recon t)) :=
    mapped_I_determined_by_T_of_screen P screen S T h_screen chi I hEIS.endogeneity
  have hzero : HcondOf P I T = 0 := by
    simpa [HcondOf] using
      (condEntropy_eq_zero_of_functionallyDetermined
        (P := P.map fun ω => (I ω, T ω))
        (recon := fun t => chi (screen.recon t)) hdet)
  linarith [hEIS.residual_autonomy, hzero]

end

end CausalQIF
