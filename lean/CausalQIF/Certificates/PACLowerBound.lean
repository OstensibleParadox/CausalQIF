import CausalQIF.Certificates.PACBounds

/-
# PAC Lower-Bound Layer

Canonical PAC lower-bound export for the paper-facing statistical derivation
entrypoint.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

namespace Certificates

export CausalQIF (pac_lower_bound_from_conditional_terms pac_lower_bound_conditional
  combine_fano_and_missed_cell_bounds pacFanoTerm pacMissedCellTerm PACPaperStatisticalDerivation
  PACPaperHypotheses pac_success_identifies_index spike_family_separated)

end Certificates

end CausalQIF
