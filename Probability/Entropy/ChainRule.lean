import CausalQIF.Probability.Entropy.ChainRule.Marginals
import CausalQIF.Probability.Entropy.ChainRule.Reshapes
import CausalQIF.Probability.Entropy.ChainRule.Bridges
import CausalQIF.Probability.Entropy.ChainRule.Decomposition

/-!
# ChainRule Module Wrapper

Re-exports the four submodules of the four-variable conditional-mutual-information
and data-processing-inequality framework:
* `ChainRule.Marginals` — seven retain-position `marginalQuad_*` projections.
* `ChainRule.Reshapes` — five `equiv*` reshapes and their `pmf*` transports.
* `ChainRule.Bridges` — five `condMutualInfo` ↔ `H+H-H-H` bridge lemmas.
* `ChainRule.Decomposition` — chain-rule identities, `condMarkov`, and the DPI corollaries.
-/
