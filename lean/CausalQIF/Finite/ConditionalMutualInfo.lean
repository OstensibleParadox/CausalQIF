import CausalQIF.InfoTheory.Conditional
import CausalQIF.InfoTheory.MutualInfo
import CausalQIF.InfoTheory.Marginal
import CausalQIF.InfoTheory.DPI

/-!
# Conditional Mutual Information and Finite Markov Predicates

Canonical finite information-theory exports for conditional mutual information,
marginalization helpers, and conditional DPI lemmas.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

namespace Finite

export CausalQIF (
  condMutualInfo
  condMutualInfo_eq_zero_of_condIndep
  condMutualInfo_nonneg
  condMutualInfo_kl_identity
  cond_dpi
  condMarkov
  condEntropy
  condEntropy_nonneg
  condProductMass
  condProductMass_nonneg
  condProductMass_sum_fiber
  condProductMass_sum_one
  condProductMass_pos_of_pmf_ne_zero
  mutualInfo
  mutualInfo_nonneg
  mutualInfo_kl_identity
  productMarginalMass
  productMarginalMass_pos_of_pmf_ne_zero
  productMarginalMass_sum_one
  sum_pmf_log_marginalLeftMass
  sum_pmf_log_marginalRightMass
  marginalTripleFstThd
  marginalTripleSndThd
  marginalTripleThd
  marginalPairFst
  marginalPairSnd
  marginalPairFst_nonneg
  marginalPairSnd_nonneg
  marginalPairFst_sum_one
  marginalPairSnd_sum_one
  marginalTripleFstThd_sum_thd
  marginalTripleSndThd_sum_thd
  marginalLeftMass
  marginalRightMass
)

end Finite

end CausalQIF
