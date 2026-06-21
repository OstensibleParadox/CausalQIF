import CausalQIF.Certificates.Tools
import CausalQIF.InfoTheory
import CausalQIF.Certificates.QuantizedBound
import CausalQIF.Certificates.IdentifiabilityGap
import CausalQIF.Certificates.CMI_Nonneg
import CausalQIF.Certificates.DualCertificate
import CausalQIF.Certificates.ChannelCapacity
import CausalQIF.Examples.CaseStudy
import CausalQIF.Certificates.CutSetBoundExtract
import CausalQIF.Certificates.TraceRecoverability
import CausalQIF.Certificates.TraceRecoverabilityBridge
import CausalQIF.Certificates.QuotientFactorization
import CausalQIF.Certificates.GeometricTools
import CausalQIF.Certificates.CoveringBound
import CausalQIF.Certificates.PACBounds
import CausalQIF.Certificates.FiniteQueryDecisionImpossibility
import CausalQIF.Certificates.PredictabilityRouteImpossibility
import CausalQIF.Certificates.SeparatedPackingImpossibility
import CausalQIF.Certificates.SemanticClosureIff
import CausalQIF.DSeparation.DAGParser
import CausalQIF.DSeparation.MarkovGenerator
import CausalQIF.DSeparation.DSepCMIBridge

/-!
# CausalQIF

Root module for the Lean verification artifact. Importing this file checks the
finite information-theory layer, finite-query impossibility cores, screenability
surrogates, certificate reductions, covering bounds, and PAC algebraic core.
-/
