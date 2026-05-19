# Debt 2 — Capacity Sufficiency via Dual KL Witness

**Date:** 2026-05-20
**Status:** Design note, not implemented.
**Companion:** `20260520_paper_repitch.md`, `20260520_debt1_factorization.md`.

---

## What Debt 2 actually is

Inspecting `CausalQIF/InformationFlow/ChannelCapacity.lean`:

```lean
def KKT_Certificate.of_direct_bound
    (P4 : FinitePMF (α × β × γ × δ))
    (C : ℝ)
    (h_bound : I_YZ_W P4 ≤ C) : KKT_Certificate P4 :=
  { C := C
    p_star      := marginalYMass P4
    per_symbol_I := fun _ => I_YZ_W P4
    h_weighted_decomp := …  -- collapses to (Σ p_star) · I_YZ_W = 1 · I_YZ_W
    h_kkt_condition   := fun _ => h_bound
    … }
```

This constructor is a **tautological wrapper**: it takes `h_bound : I_YZ_W P4 ≤ C`
as input and packages it. The "per-symbol I" is the constant `I_YZ_W P4`; the
"weighted decomposition" collapses by `∑ p_star = 1`. Zero KKT content.

`capacity_le_of_kkt` itself is correct algebra (weighted sum bound), but the
library currently contains **no constructor that produces a non-trivial
`h_bound`**. Debt 2 is exactly this gap: nothing in `CausalQIF/` derives
`I_YZ_W P4 ≤ C` from a checkable certificate.

## The verified producer — dual KL witness

Standard variational identity (Topsøe / Donsker–Varadhan):

```
I(Y; Z | W) = E_w E_{y|w} D(P(Z | y, w) ‖ P(Z | w))
            ≤ E_w E_{y|w} D(P(Z | y, w) ‖ ω(Z | w))   for any ω(z|w)
```

Quantifying the KL bound uniformly over **all** y gives capacity sufficiency:
the same witness ω caps `I_YZ_W P4` for any input distribution on Y.

This is a verified upper-bound certificate from a dual KL witness. It is
**sufficiency only**; converse (some ω achieves the capacity) and
Blahut–Arimoto convergence are not implied and remain future work.

## Framing nit — do not oversell

The math is the Topsøe / DV variational upper bound from `KL ≥ 0`. It does
**not** use concavity of the MI functional. Concavity is what makes
Blahut–Arimoto *converge to the tight bound*. The proposed theorem proves
*sufficiency of any dual witness for an upper bound*; it does **not** prove
*necessity of an optimal witness* or BA convergence. Paper-honest framing:
*"verified upper-bound certificate from a dual KL witness."* Strong because
it is exactly what an *auditor* needs.

## The `conditionalPMF` trap — avoid

Defining `P(z | y, w) = P(y, z, w) / P(y, w)` drags in:

- marginalisation commutativity over the joint;
- support theory (handling `P(y, w) = 0`);
- `0 / 0 = 0` convention;
- interaction with mathlib's `Real.log 0 = 0`.

A whole sub-theory just to state the hypothesis. Skip it.

**Phrase the variational bound under-the-integral**, with the joint
un-normalized; the conditional `P(z|y,w)` only appears implicitly as the ratio
inside `log`. `0 · log(0 / x) = 0` falls out of `Real.log` conventions and
sum bookkeeping. Saves an entire intermediate module.

Skeleton:

```lean
theorem I_YZ_W_le_of_dual_witness
    (P4 : FinitePMF (α × β × γ × δ))
    (ω : δ → γ → ℝ)
    (h_ω_sum : ∀ w, ∑ z, ω w z = 1)
    (h_ω_pos : ∀ w z, 0 < ω w z)     -- v1 simplification; weaken later
    (C : ℝ)
    (h_bound : ∀ y w,
        ∑ z, marginalYZW_at P4 y z w *
              Real.log (marginalYZW_at P4 y z w /
                        (marginalYW_at P4 y w * ω w z)) ≤
        marginalYW_at P4 y w * C) :
    I_YZ_W P4 ≤ C
```

`marginalYZW_at`, `marginalYW_at` extract the relevant joint slices; no
`conditionalPMF` term appears.

## Why this clears the debt

`I_YZ_W_le_of_dual_witness` is the missing producer. Plug into the existing
`KKT_Certificate.of_direct_bound` constructor: the `KKT_Certificate` structure
suddenly has a real source.

```
   (ω, h_ω_sum, h_ω_pos, h_bound)
            │
            ▼
   I_YZ_W_le_of_dual_witness  →  h_bound : I_YZ_W P4 ≤ C
            │
            ▼
   KKT_Certificate.of_direct_bound  →  KKT_Certificate P4
            │
            ▼
   capacity_le_of_kkt           →  I_YZ_W P4 ≤ C
```

`KKT_Certificate` stops being vacuous. Nothing downstream changes.

## Refactor — extract `klDivergence` as a first-class operator

`CausalQIF/Probability/Entropy.lean:13–` contains KL non-negativity inline but
**no first-class `klDivergence` definition**. Extract:

```lean
def klDivergence {ι : Type} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

lemma klDivergence_nonneg
    {ι : Type} [Fintype ι] (p q : ι → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hq_pos    : ∀ x, 0 < q x)
    (hp_sum_one : ∑ x, p x = 1)
    (hq_sum_one : ∑ x, q x = 1) :
    0 ≤ klDivergence p q
```

The existing proof at lines 22–55 transfers verbatim under the new name. Keep
the operator over `ι → ℝ`, **not** over `FinitePMF`, so it reuses cleanly for
both un-normalised contexts and conditional/joint slices.

## Action plan

1. **`CausalQIF/Probability/Entropy.lean`** — extract `def klDivergence` and
   `klDivergence_nonneg`. Cosmetic refactor of the existing inline proof.
   ~30 min. Verify whole `CausalQIF/` still builds zero-sorry.
2. **`CausalQIF/InformationFlow/Duality.lean`** (new) — prove
   `I_YZ_W_le_of_dual_witness` under-the-integral. Reuses `klDivergence_nonneg`
   on the joint-slice / `marginalYW × ω` ratio. Skip `conditionalPMF`.
3. **`CausalQIF/InformationFlow/ChannelCapacity.lean`** — add converter
   `KKT_Certificate.of_dual_witness`:
   ```lean
   def KKT_Certificate.of_dual_witness
       (P4 : FinitePMF (α × β × γ × δ))
       (ω : δ → γ → ℝ) (h_ω_sum h_ω_pos h_bound : …)
       (C : ℝ) : KKT_Certificate P4 :=
     KKT_Certificate.of_direct_bound P4 C
       (I_YZ_W_le_of_dual_witness P4 ω h_ω_sum h_ω_pos C h_bound)
   ```
4. **`CausalQIF/Main.lean`** — corollary
   `stateLeakage_le_of_dual_witness` composing
   `stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le` with
   `capacity_le_of_kkt ∘ KKT_Certificate.of_dual_witness`. Replaces the
   `h_cap` premise with a concrete dual-witness premise.

## Support assumption — strict positivity v1

`h_ω_pos : ∀ w z, 0 < ω w z` is strong but the right v1. Real channels are
full-support after ε-smoothing anyway. Weakening (to support hypotheses on
the joint, with the `Real.log 0 = 0` convention) is a v2 wrapper. Don't fight
support edges inside the duality theorem.

## Honest paper scope after Debt 2

Closed:

- **Sufficiency** — any dual witness `(ω, KL-bound)` mechanically yields a
  verified `I_YZ_W P4 ≤ C`, hence `stateLeakage P ≤ C`, hence
  `H(S|T̃) ≤ H(S|T_full) + C`.
- Auditor-style certificate: paper writes a section on PCC parallel
  (cf. `\cite{necula1997proof}` already in Related Work) — exhibit ω,
  machine checks KL bound, ship the bound.

Open and explicitly carried as future work:

- Converse / tightness — *some* ω achieves the capacity.
- Blahut–Arimoto convergence.
- KKT necessity (optimal `p*` characterisation).
- Weaker support hypotheses.

Worth one sentence in tech debts. Not a hole.

## Rhetorical fit with the existing paper

Paper §Related Work already cites Necula's Proof-Carrying Code. Dual-witness
sufficiency lands inside that framing exactly:

> "An auditor exhibits a dual distribution `ω` and proves an entry-wise KL
> inequality; the library mechanically converts that certificate into a
> Shannon leakage bound on the system distribution."

Strictly stronger pitch than "we mechanized Blahut–Arimoto." Honest scope,
auditor-facing payoff, fits the existing PL framing without retrofit.
