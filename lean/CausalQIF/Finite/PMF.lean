import CausalQIF.InfoTheory.Basic
import CausalQIF.InfoTheory.Entropy

/-!
# Core Finite PMF Primitives

Canonical finite-primitive re-export for the artifact's information-theory core.
This file intentionally contains only the canonical namespace boundary and import
surface for `FinitePMF` and entropy primitives.

Authors: (C) 2026 CausalQIF artifact contributors.
-/ 

namespace CausalQIF

namespace Finite

export CausalQIF (FinitePMF negMulLog2 entropyOf entropy)

end Finite

end CausalQIF
