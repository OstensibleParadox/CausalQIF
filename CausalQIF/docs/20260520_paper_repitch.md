# POPL Paper Re-Pitch — Unified `CausalQIF` Library

**Date:** 2026-05-20
**Target:** `~/Documents/popl27/paper/main.tex`
**Status:** Strategy note, not a rewrite plan.

---

## Why re-pitch

The current paper (`main.tex`) was written when the development was deliberately
split into two artifacts:

- This Lean package — d-separation equivalence + bisimulation.
- A *cited anonymous artifact* `\cite{companionqif}` carrying the quantitative
  QIF chain.

It hedges with:

- Abstract: "This paper mechanizes the graph-semantic front end; a *separate
  anonymized artifact* mechanizes the finite quantitative information-flow
  chain."
- `InfoTheoryBridge.lean` carries **two intentional `sorry` placeholders** for
  the artifact-proved bridge.
- Engineering note (App. A): "two physically separate Lake projects with
  near-isomorphic DAG definitions and no shared imports yet."
- Contribution 6 names the artifact theorems
  (`factorizes_dsep_implies_cond_indep`, `abstract_cut_set_bound`,
  `capacity_le_of_kkt`, `linear_chain_cut_set_bound_from_dag`) as cited, not
  in-repo.

All four hedges are now obsolete.

## What changed under the paper

The unified `CausalQIF` library proves the whole chain in one place,
zero-sorry across the entire `CausalQIF/` namespace:

```
d-separation  →  conditional independence  →  conditional DPI  →  cut-set bound
                          (proved in-repo: condMutualInfo_eq_zero_of_factorizes_of_dSeparates)
                                                                  ↓
                                                  stateLeakage_le_of_cutMutualInfo_le
                                                                  ↓
                                                  stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le
                                                                  ↓
                                                  certified_leakage_gap_of_dSeparated_graph
                                                       H(S|T̃) ≤ H(S|T_full) + C
```

Notable upgrades from old paper state:

- `InfoTheoryBridge.lean` 2-sorry placeholder → **bridge proved in-repo**
  (`condMutualInfo_eq_zero_of_factorizes_of_dSeparates`, `Main.lean`).
- Two-artifact split collapsed into one Lake project — the "no shared imports"
  engineering note is false now.
- New top theorem `certified_leakage_gap_of_dSeparated_graph` delivers an
  **operational entropy-gap inequality** — an auditor's bound, not a cited
  promise.
- Refinement-hook framing: `entropy_security_decomposition` (chain rule
  `H(S|T̃) = H(S|T_full) + stateLeakage`) is a `CausalQIF`-level lemma, not an
  archived `DualCertificate` fact.

## The pivot

Old spine: *"We verified a graph d-separation bisimulation (counterexample +
optimizer + decompiler); the quantitative half lives in a cited artifact."*

New spine: **"One zero-sorry Lean library carries a verified graph d-separation
judgment all the way to a machine-checked operational Shannon leakage bound."**

The bisimulation (counterexample, certified optimizer, constructive decompiler)
stops being the product. It becomes the **soundness backbone of Layer 1** of a
single end-to-end certified-security pipeline whose last theorem prints bits.

That reframes the d-separation contribution: not "we mechanized an equivalence"
but "we mechanized the *one link* that lets a graph query stand in for a
conditional-independence premise inside a real leakage proof — and here is the
leakage proof, proved, in the same artifact."

## Honesty guardrails — do not oversell

`stateLeakage_le_of_factorizes_of_dSeparates_of_cutMutualInfo_le` still **takes
as hypotheses**:

- `h_factor : FactorizesOverDAG G (fun P' _ _ _ => Probability.condMarkov P') (pmf_from_vars P cut)`
- `h_cap : cutCapacity P cut ≤ C`

So:

- **Debt 1 (Verma–Pearl).** `FactorizesOverDAG` is currently *not* product
  factorization — it is the Global Markov Property stated as an assumption
  (`∀ X Y Z, dSeparates G X Y Z → CI P X Y Z`). Deriving it from recursive
  product factorization is the open structural debt. See
  `20260520_debt1_factorization.md`.
- **Debt 2 (capacity sufficiency).** `cutCapacity P cut ≤ C` is currently
  discharged only by `KKT_Certificate.of_direct_bound`, a tautological wrapper
  that accepts the bound as input. Real sufficiency producer = dual KL witness.
  See `20260520_debt2_dual_witness.md`.
- **Debt 3 (surface calculus).** Unchanged from old paper.

The genuinely new defensible claim: **the d-sep→CI bridge is no longer a debt
or a citation — it is proved in the same zero-sorry library, and it composes
through DPI to a proved operational security bound.**

## Three pitch directions

| Spine | Headline theorem | Risk | Honesty cost |
|---|---|---|---|
| **A. Unified end-to-end** | `certified_leakage_gap_of_dSeparated_graph` | Biggest rewrite, cleanest for double-blind, drops companion-artifact conceit entirely | Must explicitly carry Debt 1 + Debt 2 as hypotheses |
| **B. Refinement-hook** | Same theorem, framed as a *verified hook* for future continuous abstraction/refinement | Sells future work | Heaviest forward claim |
| **C. Minimal de-hedge** | Old paper, but bridge upgraded from `sorry` to proved, two-artifact note removed | Low risk | Undersells the new theorem |

**Recommendation:** Direction A, with Debt 1 and Debt 2 closed (or at least
narrowed) before submission. Direction A becomes substantively stronger if the
*showcased instance* (linear chain `0→1→2`) is end-to-end with factorization
**derived** (Debt 1 instance route) and capacity **witnessed** (Debt 2 dual
witness).

## Concrete title / abstract moves under Direction A

- Drop "Beyond Boolean Intersections" — title is fine but body must finally
  earn it. Title already promises "Certified Shannon Bounds from D-Separated
  Traces" — new code delivers exactly that.
- Abstract: replace
  > "This paper mechanizes the graph-semantic front end; a separate anonymized
  > artifact mechanizes the finite quantitative information-flow chain"

  with

  > "We mechanize the full chain — d-separation, conditional independence,
  > conditional DPI, cut-set bound — as a single zero-sorry Lean 4 library,
  > whose top theorem `certified_leakage_gap_of_dSeparated_graph` derives an
  > operational entropy-gap inequality `H(S|T̃) ≤ H(S|T_full) + C` from a
  > verified graph d-separation judgment, a stated DAG factorization
  > hypothesis, and a cut-capacity certificate."

- Contribution 6 collapses into Contribution 5: the bridge is in-repo.
- Tech Debts (App. A): rewrite per `20260520_debt1_*` and `20260520_debt2_*`.
- `\cite{companionqif}` references: delete all. Single self-contained artifact.
- Engineering note ("two physically separate Lake projects"): delete.

## Open question for the rewrite

Whether to close Debt 1 instance-restricted (chain `0→1→2` only) or attempt
general derivation of `FactorizesOverDAG` from product factorization for
arbitrary DAGs. Instance route lets the headline read "**factorization derived,
not assumed, on the showcased instance**" — strictly stronger than the old
paper without overclaiming generality. See `20260520_debt1_factorization.md`.
