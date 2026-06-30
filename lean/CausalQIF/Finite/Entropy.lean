import CausalQIF.InfoTheory.Basic
import CausalQIF.InfoTheory.KL
import CausalQIF.InfoTheory.Entropy

/-!
# Entropy and KL Core

Canonical re-export for entropy-level inequalities used throughout the artifact.
Old legacy theorem names remain available through compatibility shells under
`CausalQIF.InfoTheory`.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

namespace Finite

export CausalQIF (FinitePMF
  entropy negMulLog2 entropyOf negMulLog2_nonneg entropy_nonneg entropyOf_equiv_eq
  entropyOf_mul_log2 Fintype.card_pos_of_finitePMF entropy_le_log_card
  pmf_le_one kl_nonneg kl_nonneg_support)

end Finite

end CausalQIF
