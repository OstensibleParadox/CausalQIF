import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

namespace CausalQIF

noncomputable section

/-!
# PAC Packing Lower-Bound Core

This file does **not** formalize the full Gaussian experiment, KL calculation,
Fano theorem, or missed-cell conditioning argument. Instead it formalizes the
algebraic and decision-theoretic core used by the paper's PAC packing lower
bound, and records the explicit paper-derived statistical terms:

1. the spike reward family is separated in `L1(Px)` by `alpha * tau`;
2. if a learner is within `epsilon < sep / 4` of the true reward in a separated
   family, nearest-neighbor decoding recovers the hidden cell index;
3. the paper proof supplies concrete Fano and missed-cell lower-bound terms;
4. once those two paper statistical derivations are supplied, their maximum is
   the combined sample-complexity lower bound.

The probability-theoretic derivations are the paper proof in
`provenance/fano_bound.md`; Lean checks the formula interface and the algebraic
combination.
-/

def PairwiseSeparated {ι : Type} (dist : ι → ι → ℝ) (sep : ℝ) : Prop :=
  ∀ i j : ι, i ≠ j → sep ≤ dist i j

def SpikeIndex (K : Nat) := Option (Fin K)

def spikeL1Distance {K : Nat} (alpha tau : ℝ) :
    SpikeIndex K → SpikeIndex K → ℝ
  | none, none => 0
  | none, some _ => alpha * tau
  | some _, none => alpha * tau
  | some i, some j => if i = j then 0 else 2 * alpha * tau

/--
For the spike reward family

* `R0(e) = 0`,
* `Rj(e) = tau * 1_{e ∈ Cj}`,

with disjoint cells of equal mass `alpha`, the pairwise `L1(Px)` distances are
`alpha * tau` from `R0` to each spike and `2 * alpha * tau` between distinct
spikes. Hence the family is separated at scale `alpha * tau`.
-/
theorem spike_family_separated {K : Nat} {alpha tau : ℝ}
    (h_nonneg : 0 ≤ alpha * tau) :
    PairwiseSeparated (spikeL1Distance (K := K) alpha tau) (alpha * tau) := by
  intro i j hne
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hne rfl)
      | some j => simp [spikeL1Distance]
  | some i =>
      cases j with
      | none => simp [spikeL1Distance]
      | some j =>
          have hij : i ≠ j := by
            intro hij
            exact hne (by simp [hij])
          simp [spikeL1Distance, hij]
          linarith

/--
Metric triangle interface used for nearest-neighbor decoding. `loss out i`
is the `L1(Px)` distance between the learner output and hypothesis `i`.
-/
def TriangleAgainstFamily {ι Out : Type}
    (dist : ι → ι → ℝ) (loss : Out → ι → ℝ) : Prop :=
  ∀ (out : Out) (true hyp : ι), dist true hyp ≤ loss out true + loss out hyp

/--
If the learner output is within `epsilon < sep / 4` of the true member of a
`sep`-separated family, then every wrong hypothesis is farther away than the
true one. This is Step 2 of the paper proof.
-/
theorem separated_success_makes_true_unique_nearest
    {ι Out : Type} {dist : ι → ι → ℝ} {loss : Out → ι → ℝ}
    {sep epsilon : ℝ} {out : Out} {true hyp : ι}
    (hsep : sep ≤ dist true hyp)
    (htriangle : dist true hyp ≤ loss out true + loss out hyp)
    (hloss_true_nonneg : 0 ≤ loss out true)
    (hsuccess : loss out true ≤ epsilon)
    (heps : epsilon < sep / 4) :
    loss out true < loss out hyp := by
  by_contra hnot
  have hle_hyp : loss out hyp ≤ loss out true := le_of_not_gt hnot
  have hsum : sep ≤ loss out true + loss out hyp := le_trans hsep htriangle
  have heps4 : 4 * epsilon < sep := by linarith
  have heps_nonneg : 0 ≤ epsilon := le_trans hloss_true_nonneg hsuccess
  nlinarith

/--
If `hat` is a nearest-neighbor decoder for the learner output and the learner
is within `epsilon < sep / 4` of the true reward, then `hat = true`.
-/
theorem pac_success_identifies_index
    {ι Out : Type} {dist : ι → ι → ℝ} {loss : Out → ι → ℝ}
    {sep epsilon : ℝ} {out : Out} {true hat : ι}
    (hsep : PairwiseSeparated dist sep)
    (htriangle : TriangleAgainstFamily dist loss)
    (hloss_nonneg : ∀ hyp : ι, 0 ≤ loss out hyp)
    (hsuccess : loss out true ≤ epsilon)
    (heps : epsilon < sep / 4)
    (hhat : ∀ hyp : ι, loss out hat ≤ loss out hyp) :
    hat = true := by
  by_contra hne
  have htrue_ne_hat : true ≠ hat := by
    intro h
    exact hne h.symm
  have hsep_hat : sep ≤ dist true hat := hsep true hat htrue_ne_hat
  have htri_hat : dist true hat ≤ loss out true + loss out hat :=
    htriangle out true hat
  have hlt : loss out true < loss out hat :=
    separated_success_makes_true_unique_nearest hsep_hat htri_hat (hloss_nonneg true) hsuccess heps
  have hle : loss out hat ≤ loss out true := hhat true
  linarith

/--
Once the PAC learner induces an index identifier, any lower bounds for the
resulting index-recovery problem apply to the learner. If the Fano term and
missed-cell term are both lower bounds on the sample size, their maximum is
also a lower bound.
-/
theorem combine_fano_and_missed_cell_bounds
    {m fanoTerm missedCellTerm : ℝ}
    (hfano : fanoTerm ≤ m)
    (hmissed : missedCellTerm ≤ m) :
    max fanoTerm missedCellTerm ≤ m :=
  max_le hfano hmissed

/-!
### Paper-Derived Statistical Terms

The paper proof constructs a Gaussian spike experiment with `K` disjoint cells
of mass `alpha`, spike height `tau`, observation noise `sigma`, and failure
probability `delta`. The resulting statistical lower-bound terms are recorded
as concrete Lean definitions.
-/

/--
Fano/KL term from the paper proof:

`sigma^2 / (alpha * tau^2) * (1 + 1/K)^2 *
  ((1 - delta) * log (K + 1) - log 2)`.
-/
def pacFanoTerm (K : Nat) (alpha tau sigma delta : ℝ) : ℝ :=
  (sigma ^ 2 / (alpha * tau ^ 2)) *
    (1 + 1 / (K : ℝ)) ^ 2 *
      ((1 - delta) * Real.log ((K : ℝ) + 1) - Real.log 2)

/--
Missed-cell term from the paper proof:

`log (1 / (2 * delta)) / (-log (1 - alpha))`.
-/
def pacMissedCellTerm (alpha delta : ℝ) : ℝ :=
  Real.log (1 / (2 * delta)) / (-Real.log (1 - alpha))

/--
Parameter side conditions used by the paper proof of the statistical layer.
They are recorded at the interface so the theorem statement exposes the same
domain as the handwritten argument.
-/
structure PACPaperHypotheses
    (K : Nat) (alpha tau sigma epsilon delta : ℝ) : Prop where
  K_pos : 0 < K
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  tau_pos : 0 < tau
  sigma_pos : 0 < sigma
  epsilon_pos : 0 < epsilon
  epsilon_lt_sep_quarter : epsilon < alpha * tau / 4
  delta_pos : 0 < delta
  delta_lt_half : delta < 1 / 2

/--
Concrete paper statistical derivation for the two hard paper-only arguments:

* Gaussian KL + Fano for `fano_bound`;
* missed-cell indistinguishability for `missed_cell_bound`.

The formulas are Lean-visible; the probability-theoretic proofs of the two
fields remain the external paper proof.
-/
structure PACPaperStatisticalDerivation
    (K : Nat) (m alpha tau sigma epsilon delta : ℝ) : Prop where
  hypotheses : PACPaperHypotheses K alpha tau sigma epsilon delta
  fano_bound : pacFanoTerm K alpha tau sigma delta ≤ m
  missed_cell_bound : pacMissedCellTerm alpha delta ≤ m

/-!
### Paper-Facing Conditional Theorems
-/

/--
Conditional PAC Lower Bound Wrapper.
This theorem explicitly takes the paper statistical derivation as input,
yielding the concrete combined sample-complexity lower bound.
-/
theorem pac_lower_bound_conditional
    {K : Nat} {m alpha tau sigma epsilon delta : ℝ}
    (h_ext : PACPaperStatisticalDerivation K m alpha tau sigma epsilon delta) :
    max (pacFanoTerm K alpha tau sigma delta) (pacMissedCellTerm alpha delta) ≤ m :=
  combine_fano_and_missed_cell_bounds h_ext.fano_bound h_ext.missed_cell_bound

/--
Alias matching the paper's Theorem 3 narrative for the combined result.
-/
theorem theorem3_pac_lower_bound
    {K : Nat} {m alpha tau sigma epsilon delta : ℝ}
    (h_ext : PACPaperStatisticalDerivation K m alpha tau sigma epsilon delta) :
    max (pacFanoTerm K alpha tau sigma delta) (pacMissedCellTerm alpha delta) ≤ m :=
  pac_lower_bound_conditional h_ext

end

end CausalQIF
