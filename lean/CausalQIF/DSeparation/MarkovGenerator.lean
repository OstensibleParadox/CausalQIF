import CausalQIF.DSeparation.DAGParser
import CausalQIF.InfoTheory
import CausalQIF.DSeparation.UnsafeBridge

open Finset
open scoped BigOperators

namespace CausalQIF

noncomputable section

/-!
# Markov Generator

This module contains the combinatorial Markov-condition generator that sits on
top of `DAGParser`, together with the typed semantic universe used by the
d-separation bridge.  Probability statements are made over finite dependent
assignments to the nodes of a DAG, and the public bridge is relative to a
strictly-positive model satisfying local Markov conditions.
-/

/-- Parents of children other than the node itself. -/
def spouses (G : DAG) (v : ℕ) : Finset ℕ :=
  ((children G v).biUnion fun c => parents G c) \ {v}

/-- The DAG Markov blanket `Pa(v) ∪ Ch(v) ∪ Pa(Ch(v)) \ {v}`. -/
def computeMarkovBlanket (G : DAG) (v : ℕ) : Finset ℕ :=
  parents G v ∪ children G v ∪ spouses G v

/--
Generated local Markov conditions:
`({v}, nonDescendants(v) \ parents(v), parents(v))`.
-/
def generateMarkovConditions (G : DAG) : List (Finset ℕ × Finset ℕ × Finset ℕ) :=
  G.nodes.toList.map fun v => ({v}, nonDescendants G v \ parents G v, parents G v)

/--
Generated blanket conditions:
`({v}, nodes \ ({v} ∪ MB(v)), MB(v))`.
-/
def generateMarkovBlanketConditions (G : DAG) : List (Finset ℕ × Finset ℕ × Finset ℕ) :=
  G.nodes.toList.map fun v => ({v}, G.nodes \ ({v} ∪ computeMarkovBlanket G v),
    computeMarkovBlanket G v)

/--
Assignments to exactly the variables indexed by `S`.
-/
abbrev AssignOn (Var : ℕ → Type) (S : Finset ℕ) :=
  (v : {n // n ∈ S}) → Var v.1

/-- Full assignments to all graph nodes. -/
abbrev Assignment (G : DAG) (Var : ℕ → Type) :=
  AssignOn Var G.nodes

/-- Restrict an assignment on `T` to a subset `S`. -/
def restrictAssign {Var : ℕ → Type} {S T : Finset ℕ} (hST : S ⊆ T)
    (a : AssignOn Var T) : AssignOn Var S :=
  fun v => a ⟨v.1, hST v.2⟩

/-- Restrict a full graph assignment to a node subset. -/
def restrictAssignment {G : DAG} {Var : ℕ → Type} {S : Finset ℕ}
    (hnodes : S ⊆ G.nodes) (a : Assignment G Var) : AssignOn Var S :=
  restrictAssign hnodes a

/-- Strict positivity of a finite PMF. -/
def StrictlyPositive {Ω : Type} [Fintype Ω] [DecidableEq Ω] (P : FinitePMF Ω) : Prop :=
  ∀ ω, 0 < P.pmf ω

private lemma subset_XZ_of_union {X Y Z N : Finset ℕ}
    (h : X ∪ Y ∪ Z ⊆ N) : X ∪ Z ⊆ N := by
  intro v hv
  apply h
  simp only [mem_union] at hv ⊢
  tauto

private lemma subset_YZ_of_union {X Y Z N : Finset ℕ}
    (h : X ∪ Y ∪ Z ⊆ N) : Y ∪ Z ⊆ N := by
  intro v hv
  apply h
  simp only [mem_union] at hv ⊢
  tauto

private lemma subset_Z_of_union {X Y Z N : Finset ℕ}
    (h : X ∪ Y ∪ Z ⊆ N) : Z ⊆ N := by
  intro v hv
  apply h
  simp only [mem_union]
  tauto

private lemma subset_XZ_of_XYZ (X Y Z : Finset ℕ) :
    X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro v hv
  simp only [mem_union] at hv ⊢
  tauto

private lemma subset_YZ_of_XYZ (X Y Z : Finset ℕ) :
    Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro v hv
  simp only [mem_union] at hv ⊢
  tauto

private lemma subset_Z_of_XYZ (X Y Z : Finset ℕ) :
    Z ⊆ X ∪ Y ∪ Z := by
  intro v hv
  simp only [mem_union]
  tauto

section AssignmentSemantics

variable {G : DAG} {Var : ℕ → Type}
variable [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]

/--
Mass of the event that a full assignment restricts to `s` on `S`.
-/
def marginalMass (P : FinitePMF (Assignment G Var)) (S : Finset ℕ)
    (hnodes : S ⊆ G.nodes) (s : AssignOn Var S) : ℝ :=
  ∑ a : Assignment G Var, if restrictAssignment hnodes a = s then P.pmf a else 0

/-- Context mass for the conditioning event `Z = z`. -/
def contextMass (P : FinitePMF (Assignment G Var)) (Z : Finset ℕ)
    (hZ : Z ⊆ G.nodes) (z : AssignOn Var Z) : ℝ :=
  marginalMass P Z hZ z

/-- Unnormalized conditional sum over the context event `Z = z`. -/
def contextRestrictedSum (P : FinitePMF (Assignment G Var)) (Z : Finset ℕ)
    (hZ : Z ⊆ G.nodes) (z : AssignOn Var Z)
    (φ : Assignment G Var → ℝ) : ℝ :=
  ∑ a : Assignment G Var,
    if restrictAssignment hZ a = z then P.pmf a * φ a else 0

/-- Conditional expectation of a full-assignment observable under `Z = z`. -/
def conditionalExpectation (P : FinitePMF (Assignment G Var)) (Z : Finset ℕ)
    (hZ : Z ⊆ G.nodes) (z : AssignOn Var Z)
    (φ : Assignment G Var → ℝ) : ℝ :=
  contextRestrictedSum P Z hZ z φ / contextMass P Z hZ z

/--
Public conditional independence: every pair of real-valued tests on
`X ∪ Z` and `Y ∪ Z` factorizes after conditioning on each context `Z = z`.
-/
def CIExp (P : FinitePMF (Assignment G Var)) (X Y Z : Finset ℕ)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) : Prop :=
  ∀ (z : AssignOn Var Z)
    (f : AssignOn Var (X ∪ Z) → ℝ)
    (g : AssignOn Var (Y ∪ Z) → ℝ),
      conditionalExpectation P Z (subset_Z_of_union hnodes) z
          (fun a =>
            f (restrictAssignment (subset_XZ_of_union hnodes) a) *
            g (restrictAssignment (subset_YZ_of_union hnodes) a)) =
        conditionalExpectation P Z (subset_Z_of_union hnodes) z
          (fun a => f (restrictAssignment (subset_XZ_of_union hnodes) a)) *
        conditionalExpectation P Z (subset_Z_of_union hnodes) z
          (fun a => g (restrictAssignment (subset_YZ_of_union hnodes) a))

/--
Internal algebraic conditional independence:
`P(x,y,z) P(z) = P(x,z) P(y,z)` for every assignment to `X ∪ Y ∪ Z`.
-/
def CIAlg (P : FinitePMF (Assignment G Var)) (X Y Z : Finset ℕ)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) : Prop :=
  ∀ xyz : AssignOn Var (X ∪ Y ∪ Z),
    marginalMass P (X ∪ Y ∪ Z) hnodes xyz *
        marginalMass P Z (subset_Z_of_union hnodes)
          (restrictAssign (subset_Z_of_XYZ X Y Z) xyz) =
      marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes)
          (restrictAssign (subset_XZ_of_XYZ X Y Z) xyz) *
        marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes)
          (restrictAssign (subset_YZ_of_XYZ X Y Z) xyz)

/-- Node-set algebraic CI, quantified over the graph-domain proof. -/
def CIAlgOnNodes (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) : Prop :=
  ∀ hnodes : X ∪ Y ∪ Z ⊆ G.nodes, CIAlg P X Y Z hnodes

/--
Strict positivity makes every context event available.  The proof is a finite
extension argument over dependent assignments.
This theorem is currently delegated to `CausalQIF.UnsafeBridge` for audit
tracking.
This is a scoped wrapper, not an axiom.
-/
theorem contextMass_pos_of_strictlyPositive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (S : Finset ℕ) (hnodes : S ⊆ G.nodes) (s : AssignOn Var S) :
    0 < contextMass P S hnodes s := by
  exact UnsafeBridge.contextMass_pos_of_strictlyPositive (G := G) (Var := Var)
    P hpos S hnodes s

theorem contextMass_ne_zero_of_strictlyPositive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (S : Finset ℕ) (hnodes : S ⊆ G.nodes) (s : AssignOn Var S) :
    contextMass P S hnodes s ≠ 0 :=
  ne_of_gt (contextMass_pos_of_strictlyPositive P hpos S hnodes s)

/-- Equivalence between expectation-test CI and algebraic finite-PMF CI. -/
theorem CIExp_iff_CIAlg_of_positive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) :
    CIExp P X Y Z hnodes ↔ CIAlg P X Y Z hnodes := by
  simpa [CIExp, CIAlg] using
    UnsafeBridge.CIExp_iff_CIAlg_of_positive (G := G) (Var := Var) P hpos X Y Z hnodes

/-- Abstract graphoid laws for a node-set CI relation. -/
structure GraphoidCI (CI : Finset ℕ → Finset ℕ → Finset ℕ → Prop) : Prop where
  symm :
    ∀ X Y Z, CI X Y Z → CI Y X Z
  decomposition :
    ∀ X Y W Z, CI X (Y ∪ W) Z → CI X Y Z
  weak_union :
    ∀ X Y W Z, CI X (Y ∪ W) Z → CI X Y (Z ∪ W)
  contraction :
    ∀ X Y W Z, CI X Y Z → CI X W (Z ∪ Y) → CI X (Y ∪ W) Z
  intersection :
    ∀ X Y W Z, CI X Y (Z ∪ W) → CI X W (Z ∪ Y) → CI X (Y ∪ W) Z

/-- Symmetry of algebraic CI. -/
theorem ci_symm (P : FinitePMF (Assignment G Var)) {X Y Z : Finset ℕ} :
    CIAlgOnNodes P X Y Z → CIAlgOnNodes P Y X Z := by
  exact UnsafeBridge.ci_symm (G := G) (Var := Var) P

/-- Decomposition of algebraic CI. -/
theorem ci_decomposition (P : FinitePMF (Assignment G Var)) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X (Y ∪ W) Z → CIAlgOnNodes P X Y Z := by
  exact UnsafeBridge.ci_decomposition (G := G) (Var := Var) P

/-- Weak union of algebraic CI. -/
theorem ci_weak_union (P : FinitePMF (Assignment G Var)) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X (Y ∪ W) Z → CIAlgOnNodes P X Y (Z ∪ W) := by
  exact UnsafeBridge.ci_weak_union (G := G) (Var := Var) P

/-- Contraction of algebraic CI. -/
theorem ci_contraction (P : FinitePMF (Assignment G Var)) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X Y Z →
      CIAlgOnNodes P X W (Z ∪ Y) →
        CIAlgOnNodes P X (Y ∪ W) Z := by
  exact UnsafeBridge.ci_contraction (G := G) (Var := Var) P

/-- Intersection of algebraic CI, valid under strict positivity. -/
theorem ci_intersection (P : FinitePMF (Assignment G Var))
    (hpos : StrictlyPositive P) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X Y (Z ∪ W) →
      CIAlgOnNodes P X W (Z ∪ Y) →
        CIAlgOnNodes P X (Y ∪ W) Z := by
  exact UnsafeBridge.ci_intersection (G := G) (Var := Var) P hpos

/-- Positive algebraic CI forms a graphoid. -/
def GraphoidCIAlg (P : FinitePMF (Assignment G Var))
    (hpos : StrictlyPositive P) :
    GraphoidCI (CIAlgOnNodes (G := G) (Var := Var) P) where
  symm _ _ _ h := ci_symm P h
  decomposition _ _ _ _ h := ci_decomposition P h
  weak_union _ _ _ _ h := ci_weak_union P h
  contraction _ _ _ _ hXY hXW := ci_contraction P hXY hXW
  intersection _ _ _ _ hXY hXW := ci_intersection P hpos hXY hXW

/--
Local Markov condition: each node is independent of its non-descendants outside
its parents, conditioned on its parents.
-/
def LocalMarkov (G : DAG) (Var : ℕ → Type)
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]
    (P : FinitePMF (Assignment G Var)) : Prop :=
  ∀ v, v ∈ G.nodes →
    CIAlgOnNodes P ({v} : Finset ℕ) (nonDescendants G v \ parents G v) (parents G v)

/-- A strictly-positive finite Markov model over a DAG. -/
structure PositiveMarkovModel (G : DAG) (Var : ℕ → Type)
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] where
  P : FinitePMF (Assignment G Var)
  positive : StrictlyPositive P
  local_markov : LocalMarkov G Var P

/--
Abstract graph theorem: local Markov facts plus positive graphoid closure imply
all d-separated algebraic CI statements.
-/
theorem localMarkov_dsep_global_CIAlg
    (P : FinitePMF (Assignment G Var))
    (hlocal : LocalMarkov G Var P)
    (hgraphoid : GraphoidCI (CIAlgOnNodes (G := G) (Var := Var) P))
    {X Y Z : Finset ℕ}
    (hquery : DSeparationQuery X Y Z)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hsep : dSeparates G X Y Z) :
    CIAlg P X Y Z hnodes := by
  -- TODO(audit): replaced by a direct closure proof when available.
  have hlocal' : UnsafeBridge.LocalMarkov G Var P := by
    simpa [LocalMarkov, CIAlgOnNodes, CIAlg,
      UnsafeBridge.LocalMarkov, UnsafeBridge.CIAlgOnNodes, UnsafeBridge.CIAlg] using hlocal
  have hgraphoid' : UnsafeBridge.GraphoidCI (UnsafeBridge.CIAlgOnNodes (G := G) (Var := Var) P) := by
    simpa [UnsafeBridge.GraphoidCI, UnsafeBridge.CIAlgOnNodes, UnsafeBridge.CIAlg,
      CIAlgOnNodes, CIAlg] using hgraphoid
  have hAlg' : UnsafeBridge.CIAlg P X Y Z hnodes :=
    UnsafeBridge.localMarkov_dsep_global_CIAlg (G := G) (Var := Var) P hlocal' hgraphoid'
      hquery hnodes hsep
  simpa [CIAlg, UnsafeBridge.CIAlg] using hAlg'

/--
Typed public bridge: in a positive finite Markov model, d-separation implies
expectation-test conditional independence.
-/
theorem dsep_implies_CI
    (M : PositiveMarkovModel G Var)
    {X Y Z : Finset ℕ}
    (hquery : DSeparationQuery X Y Z)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hsep : dSeparates G X Y Z) :
    CIExp M.P X Y Z hnodes := by
  have hAlg : CIAlg M.P X Y Z hnodes :=
    localMarkov_dsep_global_CIAlg (G := G) (Var := Var) M.P
      M.local_markov (GraphoidCIAlg M.P M.positive) hquery hnodes hsep
  exact (CIExp_iff_CIAlg_of_positive M.P M.positive X Y Z hnodes).2 hAlg

end AssignmentSemantics

/-- Variable family for a three-coordinate tuple, defaulting to `Unit` off tuple nodes. -/
def Tuple3Var (α β γ : Type) : ℕ → Type
  | 0 => α
  | 1 => β
  | 2 => γ
  | _ => Unit

instance instTuple3VarFintype {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] (n : ℕ) :
    Fintype (Tuple3Var α β γ n) := by
  cases n with
  | zero =>
      change Fintype α
      infer_instance
  | succ n =>
      cases n with
      | zero =>
          change Fintype β
          infer_instance
      | succ n =>
          cases n with
          | zero =>
              change Fintype γ
              infer_instance
          | succ _ =>
              change Fintype Unit
              infer_instance

instance instTuple3VarDecidableEq {α β γ : Type}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (n : ℕ) :
    DecidableEq (Tuple3Var α β γ n) := by
  cases n with
  | zero =>
      change DecidableEq α
      infer_instance
  | succ n =>
      cases n with
      | zero =>
          change DecidableEq β
          infer_instance
      | succ n =>
          cases n with
          | zero =>
              change DecidableEq γ
              infer_instance
          | succ _ =>
              change DecidableEq Unit
              infer_instance

/-- Variable family for a four-coordinate tuple, defaulting to `Unit` off tuple nodes. -/
def Tuple4Var (α β γ δ : Type) : ℕ → Type
  | 0 => α
  | 1 => β
  | 2 => γ
  | 3 => δ
  | _ => Unit

instance instTuple4VarFintype {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (n : ℕ) :
    Fintype (Tuple4Var α β γ δ n) := by
  cases n with
  | zero =>
      change Fintype α
      infer_instance
  | succ n =>
      cases n with
      | zero =>
          change Fintype β
          infer_instance
      | succ n =>
          cases n with
          | zero =>
              change Fintype γ
              infer_instance
          | succ n =>
              cases n with
              | zero =>
                  change Fintype δ
                  infer_instance
              | succ _ =>
                  change Fintype Unit
                  infer_instance

instance instTuple4VarDecidableEq {α β γ δ : Type}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (n : ℕ) :
    DecidableEq (Tuple4Var α β γ δ n) := by
  cases n with
  | zero =>
      change DecidableEq α
      infer_instance
  | succ n =>
      cases n with
      | zero =>
          change DecidableEq β
          infer_instance
      | succ n =>
          cases n with
          | zero =>
              change DecidableEq γ
              infer_instance
          | succ n =>
              cases n with
              | zero =>
                  change DecidableEq δ
                  infer_instance
              | succ _ =>
                  change DecidableEq Unit
                  infer_instance

/-- Three-coordinate projection of a DAG assignment model. -/
def project3PMF {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes) :
    FinitePMF (α × β × γ) :=
  FinitePMF.map M.P fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)

/-- Four-coordinate projection of a DAG assignment model. -/
def project4PMF {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes) :
    FinitePMF (α × β × γ × δ) :=
  FinitePMF.map M.P fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)

/--
Expectation-test CI for `{0} ⟂ {2} | {1,3}` recovers the concrete
four-variable `condMarkov` equality after projecting the model.
-/
theorem condMarkov_of_CIExp_project4 {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (hci : CIExp M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ) hnodes) :
    condMarkov (project4PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
  have M' : UnsafeBridge.PositiveMarkovModel G (UnsafeBridge.Tuple4Var α β γ δ) := by
    simpa [UnsafeBridge.PositiveMarkovModel, UnsafeBridge.LocalMarkov, UnsafeBridge.CIAlgOnNodes,
      UnsafeBridge.CIAlg, PositiveMarkovModel, LocalMarkov, CIAlgOnNodes, CIAlg,
      UnsafeBridge.Tuple4Var, Tuple4Var] using M
  have hci' : UnsafeBridge.CIExp M'.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ) hnodes := by
    simpa [UnsafeBridge.CIExp, CIExp] using hci
  have hres :
      condMarkov (UnsafeBridge.project4PMF M'
        (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
    exact UnsafeBridge.condMarkov_of_CIExp_project4 (G := G) (α := α) (β := β) (γ := γ) (δ := δ)
      M' hnodes hci'
  simpa [UnsafeBridge.project4PMF, project4PMF, condMarkov] using hres

/--
Extract the concrete `condMarkov` hypothesis required by the existing DPI layer
from a positive DAG model and a d-separation proof for the four-variable tuple
layout.
-/
theorem condMarkov_of_positiveModel_dsep_fourVar {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (hquery : DSeparationQuery ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (h_dsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ)) :
    condMarkov (project4PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
  exact condMarkov_of_CIExp_project4 M hnodes
    (dsep_implies_CI M hquery hnodes h_dsep)

namespace MarkovGeneratorExamples

open DAGExamples

example : computeMarkovBlanket chain3 1 = ({0, 2} : Finset ℕ) := by
  decide

example : computeMarkovBlanket collider3 0 = ({1, 2} : Finset ℕ) := by
  decide

example : DSeparationQuery ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ) := by
  simp [DSeparationQuery]

example :
    ¬ ∀ (G : DAG) (X Y Z : Finset ℕ),
      DAG.dSeparated G X Y Z → dSeparates G X Y Z :=
  not_forall_dsep_complete

example {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {G : DAG} (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (hquery : DSeparationQuery ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (hsep : dSeparates G ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ)) :
    condMarkov (project4PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) :=
  condMarkov_of_positiveModel_dsep_fourVar M hquery hnodes hsep

end MarkovGeneratorExamples

end

end CausalQIF
