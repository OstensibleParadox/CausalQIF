import CausalQIF.DSeparation.DAGParser
import CausalQIF.InfoTheory

open Finset
open scoped BigOperators
namespace CausalQIF.UnsafeBridge

noncomputable section

section AssignmentSemantics

variable {G : DAG} {Var : ℕ → Type}
variable [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]

/-!
Audit bridge for unclosed assumptions in the d-separation ↔ CI layer.

This file intentionally contains the remaining axioms that are known and
tracked. `MarkovGenerator` re-exports them as theorems so downstream bridges
do not depend on raw `axiom` declarations.
-/

abbrev AssignOn (Var : ℕ → Type) (S : Finset ℕ) :=
  (v : {n // n ∈ S}) → Var v.1

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

/-- Mass of the event that a full assignment restricts to `s` on `S`. -/
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

/-- Internal algebraic conditional independence. -/
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

/-- Public node-set algebraic CI, quantified over node proofs. -/
def CIAlgOnNodes (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) : Prop :=
  ∀ hnodes : X ∪ Y ∪ Z ⊆ G.nodes, CIAlg P X Y Z hnodes

/-- Expectation-test CI. -/
def CIExp (P : FinitePMF (Assignment G Var)) (X Y Z : Finset ℕ)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) : Prop :=
  ∀ (z : AssignOn Var Z)
    (f : AssignOn Var (X ∪ Z) → ℝ)
    (g : AssignOn Var (Y ∪ Z) → ℝ),
      conditionalExpectation P Z (subset_Z_of_union hnodes) z
          (fun a =>
            f (restrictAssign (subset_XZ_of_union hnodes) a) *
            g (restrictAssign (subset_YZ_of_union hnodes) a)) =
        conditionalExpectation P Z (subset_Z_of_union hnodes) z
          (fun a => f (restrictAssign (subset_XZ_of_union hnodes) a)) *
        conditionalExpectation P Z (subset_Z_of_union hnodes) z
          (fun a => g (restrictAssign (subset_YZ_of_union hnodes) a))

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

/-- Local Markov condition in terms of algebraic CI. -/
def LocalMarkov (G : DAG) (Var : ℕ → Type)
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]
    (P : FinitePMF (Assignment G Var)) : Prop :=
  ∀ v, v ∈ G.nodes →
    CIAlgOnNodes P ({v} : Finset ℕ) (nonDescendants G v \ parents G v) (parents G v)

/-- Positive finite Markov model over a DAG. -/
structure PositiveMarkovModel (G : DAG) (Var : ℕ → Type)
    [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] where
  P : FinitePMF (Assignment G Var)
  positive : StrictlyPositive P
  local_markov : LocalMarkov G Var P

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

/-- Three-coordinate projection of a DAG assignment model. -/
def project3PMF {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes) :
    FinitePMF (α × β × γ) :=
  FinitePMF.map M.P fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)

/-- Unsafe marker Markov-chain formula for three variables. -/
abbrev UnsafeIsMarkovChain {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : FinitePMF (α × β × γ)) : Prop :=
  ∀ a b c,
    P.pmf (a, b, c) * (∑ a' : α, ∑ c' : γ, P.pmf (a', b, c')) =
      (∑ c' : γ, P.pmf (a, b, c')) * (∑ a' : α, P.pmf (a', b, c))

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

/-- Four-coordinate projection of a DAG assignment model. -/
def project4PMF {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
  (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes) :
    FinitePMF (α × β × γ × δ) :=
  FinitePMF.map M.P fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)

-- Keep the variable context for unsafe axioms aligned with `MarkovGenerator` APIs.
variable {G : DAG} {Var : ℕ → Type}
variable [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]

-- Pending audit entry: positivity of context mass.
axiom contextMass_pos_of_strictlyPositive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (S : Finset ℕ) (hnodes : S ⊆ G.nodes) (s : AssignOn Var S) :
    0 < contextMass P S hnodes s

-- Pending audit entry: `CIExp` ↔ `CIAlg` under positivity.
axiom CIExp_iff_CIAlg_of_positive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) :
    CIExp P X Y Z hnodes ↔ CIAlg P X Y Z hnodes

-- Pending audit entry: graphoid closure laws on `CIAlg`.
axiom ci_symm (P : FinitePMF (Assignment G Var)) {X Y Z : Finset ℕ} :
    CIAlgOnNodes P X Y Z → CIAlgOnNodes P Y X Z

axiom ci_decomposition (P : FinitePMF (Assignment G Var)) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X (Y ∪ W) Z → CIAlgOnNodes P X Y Z

axiom ci_weak_union (P : FinitePMF (Assignment G Var)) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X (Y ∪ W) Z → CIAlgOnNodes P X Y (Z ∪ W)

axiom ci_contraction (P : FinitePMF (Assignment G Var)) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X Y Z →
      CIAlgOnNodes P X W (Z ∪ Y) →
        CIAlgOnNodes P X (Y ∪ W) Z

axiom ci_intersection (P : FinitePMF (Assignment G Var))
    (hpos : StrictlyPositive P) {X Y W Z : Finset ℕ} :
    CIAlgOnNodes P X Y (Z ∪ W) →
      CIAlgOnNodes P X W (Z ∪ Y) →
        CIAlgOnNodes P X (Y ∪ W) Z

/-- Pending audit entry: global graph-analytic bridge from local Markov + graphoid to d-separation.
This currently depends on the above algebraic closure assumptions. -/
axiom localMarkov_dsep_global_CIAlg
    (P : FinitePMF (Assignment G Var))
    (hlocal : LocalMarkov G Var P)
    (hgraphoid : GraphoidCI (CIAlgOnNodes (G := G) (Var := Var) P))
    {X Y Z : Finset ℕ}
    (hquery : DSeparationQuery X Y Z)
    (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hsep : dSeparates G X Y Z) :
    CIAlg P X Y Z hnodes

-- Pending audit entry: three-variable projection bridge.
axiom isMarkovChain_of_CIExp_project3 {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (hci : CIExp M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ) hnodes) :
    UnsafeIsMarkovChain (project3PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)))

-- Pending audit entry: four-variable projection bridge.
axiom condMarkov_of_CIExp_project4 {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (hci : CIExp M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ) hnodes) :
    condMarkov (project4PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)))

end AssignmentSemantics

end

end CausalQIF.UnsafeBridge
