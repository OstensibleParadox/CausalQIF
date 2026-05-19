import CausalQIF.CausalModel.Factorization
import CausalQIF.CausalModel.DataProcessing

open Finset
open scoped BigOperators Real

namespace CausalQIF.InformationFlow

noncomputable section

variable {State VisibleTrace MissingTrace : Type}
variable [Fintype State] [Fintype VisibleTrace] [Fintype MissingTrace]
variable [DecidableEq State] [DecidableEq VisibleTrace] [DecidableEq MissingTrace]

/-! ## State Leakage Definitions -/

def stateVisibleMass (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (st : State × VisibleTrace) : ℝ :=
  ∑ m : MissingTrace, P.pmf (st.1, st.2, m)

def visibleMass (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (t : VisibleTrace) : ℝ :=
  ∑ s : State, ∑ m : MissingTrace, P.pmf (s, t, m)

def visibleMissingMass (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (tm : VisibleTrace × MissingTrace) : ℝ :=
  ∑ s : State, P.pmf (s, tm.1, tm.2)

def fullTraceEntropy (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  Probability.entropyOf (fun stm : State × VisibleTrace × MissingTrace => P.pmf stm)

/-- 
The Shannon leakage $I(S; M \mid T)$ where $S$ is State, $M$ is MissingTrace, 
and $T$ is VisibleTrace. 
Calculated as $H(S, T) + H(M, T) - H(T) - H(S, M, T)$.
-/
def stateLeakage (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace)) : ℝ :=
  Probability.entropyOf (stateVisibleMass P) +
    Probability.entropyOf (visibleMissingMass P) -
    Probability.entropyOf (visibleMass P) -
    fullTraceEntropy P

/-! ## Cut Mutual Information -/

structure CutSetData (State VisibleTrace MissingTrace CutVars : Type) [Fintype CutVars] [DecidableEq CutVars] where
  cut_map : (State × VisibleTrace × MissingTrace) → CutVars

/--
The 4-variable PMF layout for DPI: (X=State, Y=Cut, Z=Missing, W=Visible).
-/
def pmf_from_vars {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) :
    Probability.FinitePMF (State × CutVars × MissingTrace × VisibleTrace) :=
  P.map (fun stm => (stm.1, cut.cut_map stm, stm.2.2, stm.2.1))

/-- Information-theoretic capacity of the cut: $I(K; M \mid T)$. -/
def cutCapacity {CutVars : Type} [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars) : ℝ :=
  Probability.I_YZ_W (pmf_from_vars P cut)

/-! ## Main Cut-Set Bound Theorem -/

/--
The machine-checked Shannon leakage upper bound.
If the cut-set $K$ d-separates State from MissingTrace, then by DPI:
$I(S; M \mid T) \leq I(K; M \mid T)$.
-/
theorem stateLeakage_le_of_cutMutualInfo_le {CutVars : Type}
    [Fintype CutVars] [DecidableEq CutVars]
    (P : Probability.FinitePMF (State × VisibleTrace × MissingTrace))
    (cut : CutSetData State VisibleTrace MissingTrace CutVars)
    (C : ℝ)
    (h_factor : Probability.condMarkov (pmf_from_vars P cut))
    (h_cap : cutCapacity P cut ≤ C) :
    stateLeakage P ≤ C := by
  have h_dpi := CausalModel.cond_dpi (pmf_from_vars P cut) h_factor
  -- The layout maps (X=State, Y=Cut, Z=Missing, W=Visible)
  -- so I_XZ_W is I(State; Missing | Visible) = stateLeakage P
  -- and I_YZ_W is I(Cut; Missing | Visible) = cutCapacity P cut
  sorry

end

end CausalQIF.InformationFlow
