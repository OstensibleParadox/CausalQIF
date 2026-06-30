import CausalQIF.Certificates.Tools
import CausalQIF.Finite.ConditionalMutualInfo
import CausalQIF.Graph.MarkovBridge
import CausalQIF.Certificates.IdentifiabilityGap
import CausalQIF.Certificates.StaticCutBound
import CausalQIF.Certificates.DynamicProbeBound
import CausalQIF.Certificates.PACLowerBound
import CausalQIF.Certificates.CMI_Nonneg
import CausalQIF.Certificates.ChannelCapacity
import CausalQIF.Examples.LinearChain
import CausalQIF.Certificates.CutSetBoundExtract
import CausalQIF.Certificates.TraceRecoverability
import CausalQIF.Certificates.TraceRecoverabilityBridge
import CausalQIF.Certificates.QuotientFactorization
import CausalQIF.Certificates.GeometricTools
import CausalQIF.Certificates.CoveringBound
import CausalQIF.Certificates.FiniteQueryDecisionImpossibility
import CausalQIF.Certificates.EntropicEIS
import CausalQIF.Certificates.SeparatedPackingImpossibility
import CausalQIF.Certificates.SemanticClosureIff
import CausalQIF.Certificates.QuantizationBound
import CausalQIF.Paper.MainTheorems

/-!
# CausalQIF

Root module for the Lean verification artifact. Importing this file checks the
finite information-theory layer, finite-query impossibility cores, screenability
surrogates, certificate reductions, covering bounds, and PAC algebraic core.
-/
