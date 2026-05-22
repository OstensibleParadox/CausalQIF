import CausalQIF.Probability.FinitePMF.Basic
import CausalQIF.Probability.FinitePMF.Entropy
import CausalQIF.Probability.FinitePMF.Marginal

/-!
# FinitePMF Module Wrapper

Re-exports the three submodules of the discrete-PMF foundation:
* `FinitePMF.Basic` — the `FinitePMF` structure, `comapEquiv`, `map`.
* `FinitePMF.Entropy` — base-2 entropy and its core lemmas.
* `FinitePMF.Marginal` — 2- and 3-tuple marginals, leaf marginalization, pullback lemmas.

The sibling submodule `FinitePMF.Marginalize` (4→3 projections) imports this
wrapper directly; it is exported by the root `CausalQIF` module.
-/
