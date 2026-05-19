# Debt 1 — Deriving `FactorizesOverDAG` from Product Factorization

**Date:** 2026-05-20
**Status:** Design note, not implemented.
**Companion:** `20260520_paper_repitch.md`, `20260520_debt2_dual_witness.md`.

---

## What Debt 1 actually is

Inspecting `CausalQIF/CausalModel/Factorization.lean`:

```lean
abbrev CondIndepPredicate (Ω : Type) [Fintype Ω] [DecidableEq Ω]
    (V : Type) [DecidableEq V] [Fintype V] :=
  Probability.FinitePMF Ω → Finset V → Finset V → Finset V → Prop

def FactorizesOverDAG {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    {V : Type} [DecidableEq V] [Fintype V]
    (G : Graph.DAG V) (CI : CondIndepPredicate Ω V)
    (P : Probability.FinitePMF Ω) : Prop :=
  ∀ X Y Z : Finset V, DSeparation.dSeparates G X Y Z → CI P X Y Z
```

`FactorizesOverDAG` is **not** product factorization. It **is** the Global
Markov Property stated as an assumption: "d-separation implies the CI
predicate." It is parameterised by whatever `CI` predicate the caller plugs in
(e.g. `isMarkovChainNodeCI`, which itself is a thin pattern-matched adapter).

The in-repo "bridge" `condMutualInfo_eq_zero_of_factorizes_of_dSeparates` is a
near-tautological unwrap of this hypothesis composed with the genuine
information-theoretic fact `condMutualInfo_eq_zero_of_isMarkovChain`. The
d-sep→CI step is **assumed, not derived**.

Debt 1 = derive `FactorizesOverDAG` from a recursive product factorization
`P(V) = ∏_i P(v_i ∣ parents(v_i))`.

## Why the textbook strategy is the hardest possible route

Textbook route is Lauritzen–Verma–Pearl:

1. Define product factorization on `(v : V) → Ω v`.
2. Prove Local Markov: each node ⊥⊥ non-descendants ∣ parents.
3. Prove Local ⇒ Global Markov (d-separation soundness).

Step 3 in full DAG generality is the **ordered-Markov / topological-order /
moralization metatheorem**. This is a mathlib-scale formalization, not a port.
It is exactly the scientific content the old paper deferred on purpose.

## Representation problem — bigger than first sketched

Not merely "flat `α` vs `(v : V) → Ω v`." The **entire downstream zero-sorry
chain** is hardwired to flat tuples:

- `pmf_from_vars : FinitePMF (State × VisibleTrace × MissingTrace) → FinitePMF (State × CutVars × MissingTrace × VisibleTrace)`
- `stateLeakage` defined via masses on `State × VisibleTrace × MissingTrace`.
- All four marginal-mass lemmas in `InformationFlow/CutSetBound.lean`.
- `isMarkovChainNodeCI` pattern-matches the specific singleton sets `{v0}`,
  `{v1}`, `{v2}`.

**Do not retype the QIF core.** It is zero-sorry; perturbing it is pure loss.

## Correct architectural seam

Put product factorization **strictly upstream** of `FactorizesOverDAG`, and
provide a marshalling lemma onto the flat tuple PMF the chain consumes.

```
   ProductFactorizes G P       (new module, on Cfg V Ω := (v : V) → Ω v)
            │ prove ⇒
            ▼
   FactorizesOverDAG G CI P    (was an assumption — becomes a derived lemma)
            │  unchanged
            ▼
   zero-sorry QIF chain         (untouched)
```

Target theorem:

```lean
theorem factorizesOverDAG_of_productFactorizes
    {V : Type} [DecidableEq V] [Fintype V]
    {Ω : V → Type} [∀ v, Fintype (Ω v)] [∀ v, DecidableEq (Ω v)]
    (G : Graph.DAG V) (P : Probability.FinitePMF ((v : V) → Ω v))
    (h : ProductFactorizes G P) :
    FactorizesOverDAG G CI (marshall P)
```

where `marshall` projects the dependent-config PMF onto the flat tuple type the
chain uses. Nothing downstream changes.

## Two levers — both available, both cheaper than the textbook route

### Lever 1 — Reuse the verified moral-graph engine

The artifact already contains `dSeparated_iff_dSeparates` and the moral-graph
bisimulation. That is **exactly** the separation theory Step 3 needs. Route
factorization → Global Markov *through the existing verified moral-graph
reachability* rather than re-deriving separation. Layer 1 (the paper's current
product) becomes the **engine that discharges Debt 1**. Major structural
payoff for the re-pitch: the bisimulation isn't just a front-end contribution
— it is the lever that closes the Verma–Pearl gap.

### Lever 2 — Instance escape hatch

The paper showcases the linear chain `0 → 1 → 2` (`isMarkovChainNodeCI v0 v1 v2`,
`linear_chain_cut_set_bound_from_dag`). For one fixed small DAG,
*product factorization ⇒ `IsMarkovChain P`* is a **direct computation** — no
general metatheorem. That removes the assumed `FactorizesOverDAG` for the
instance the paper actually claims.

Re-pitch consequence (see `20260520_paper_repitch.md`): the headline can read
**"end-to-end on the showcased instance with factorization derived, not
assumed."** Strictly stronger than the old paper, without overclaiming
generality.

## Decision fork

| Route | Effort | Scope cleared | Risk |
|---|---|---|---|
| **General DAG** | Months. Mathlib-scale ordered-Markov / moralization metatheorem. Or reuse Lever 1, which softens it but is still substantial. | All instances. Debt 1 fully closed. | High — formalisation risk + scope creep. |
| **Instance-restricted (chain `0→1→2`)** | Weeks. Direct computation on the showcased DAG. | Showcased instance only. Headline becomes "factorization derived on instance; general derivation = future work." | Low. Bounded scope. |

## Recommended plan

1. Pick **instance-restricted** for POPL submission.
2. Implement upstream module
   `CausalQIF/CausalModel/ProductFactorization.lean`:
   - `ProductFactorizes_chain3 G v0 v1 v2 P` (specialised predicate for the
     three-node chain).
   - `factorizesOverDAG_isMarkovChain_of_productFactorizes_chain3` proving
     `ProductFactorizes_chain3 ... → FactorizesOverDAG G (isMarkovChainNodeCI v0 v1 v2) P`.
3. Marshalling: state directly on the flat `α × β × γ` type the chain uses; no
   dependent-config layer needed for the chain instance.
4. Defer the general theorem to "Future work — general Verma–Pearl mechanization."
5. Open `CausalQIF.CausalModel.ProductFactorization` namespace; do **not** edit
   `Factorization.lean` (preserve current `FactorizesOverDAG` as the existing
   parametric hypothesis interface; new lemma is a *producer* of that
   hypothesis).

## What to NOT do

- Do not redefine `FinitePMF` over dependent configs. The QIF chain depends on
  flat-tuple `FinitePMF`. Independent representation, marshall at the seam.
- Do not edit any file under `CausalQIF/InformationFlow/` or `CausalQIF/Probability/`.
  The zero-sorry chain is load-bearing; perturbing it risks regression.
- Do not chase the general theorem first. Instance lemma first; general theorem
  as future work.

## Honest framing of the closed scope

Even with the instance route, the paper claim is bounded:

- Closed: on the linear chain `0→1→2`, product factorization ⇒ `IsMarkovChain`
  ⇒ `condMutualInfo = 0`, all in `CausalQIF`, zero-sorry.
- Open: general DAG `FactorizesOverDAG`. Listed as future work.

This matches the paper's existing precedent of using the linear chain as the
worked end-to-end instance (`linear_chain_cut_set_bound_from_dag`).
