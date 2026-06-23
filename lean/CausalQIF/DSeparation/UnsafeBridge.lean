import CausalQIF.DSeparation.DAGParser
import CausalQIF.InfoTheory

open Finset
open scoped BigOperators
namespace CausalQIF.UnsafeBridge

noncomputable section

section AssignmentSemantics

variable {G : DAG} {Var : ℕ → Type}
variable [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]

/-- Core typed assignment semantics shared by the bridge. -/
abbrev AssignOn (Var : ℕ → Type) (S : Finset ℕ) :=
  (v : {n // n ∈ S}) → Var v.1

abbrev Assignment (G : DAG) (Var : ℕ → Type) :=
  AssignOn Var G.nodes

/-- Restrict an assignment on `T` to a subset `S`. -/
def restrictAssign {Var : ℕ → Type} {S T : Finset ℕ}
    (hST : S ⊆ T) (a : AssignOn Var T) : AssignOn Var S :=
  fun v => a ⟨v.1, hST v.2⟩

/-- Restrict a full graph assignment to a node subset. -/
def restrictAssignment {G : DAG} {Var : ℕ → Type} {S : Finset ℕ}
    (hnodes : S ⊆ G.nodes) (a : Assignment G Var) : AssignOn Var S :=
  restrictAssign hnodes a

/-- Strict positivity of a finite PMF. -/
def StrictlyPositive {Ω : Type} [Fintype Ω] [DecidableEq Ω] (P : FinitePMF Ω) : Prop :=
  ∀ ω, 0 < P.pmf ω

private def Reindex {S T : Finset ℕ}
    (h : ∀ n, n ∈ S ↔ n ∈ T)
    (a : AssignOn Var S) : AssignOn Var T :=
  fun i => a ⟨i.1, (h i.1).2 i.2⟩

private theorem reindex_inv
    {S T : Finset ℕ} (hST : ∀ n, n ∈ S ↔ n ∈ T)
    (a : AssignOn Var S) :
    Reindex (fun n => (hST n).symm) (Reindex hST a) = a := by
  ext t
  cases t with
  | mk n hn =>
      simp [Reindex]

private theorem reindex_restrict
    {S T U : Finset ℕ}
    (hST : ∀ n, n ∈ S ↔ n ∈ T)
    (hSU : U ⊆ S) (hTU : U ⊆ T)
    (a : AssignOn Var S) (u : {n // n ∈ U}) :
    restrictAssign hTU (Reindex hST a) u = restrictAssign hSU a u := by
  simp [Reindex, restrictAssign]

private theorem reindex_restrictAssignment_eq
    {S T : Finset ℕ} (hST : ∀ n, n ∈ S ↔ n ∈ T)
    (hS : S ⊆ G.nodes) (hT : T ⊆ G.nodes)
    (a : Assignment G Var) :
    Reindex (fun n => (hST n).symm) (restrictAssignment (G := G) hT a) =
      restrictAssignment (G := G) hS a := by
  ext t
  cases t with
  | mk n hn =>
      simp [Reindex, restrictAssign, restrictAssignment]

private theorem restrict_assign_eq_iff
    {S T : Finset ℕ} (hST : ∀ n, n ∈ S ↔ n ∈ T)
    (hS : S ⊆ G.nodes) (hT : T ⊆ G.nodes)
    (a : Assignment G Var)
    (s : AssignOn Var S) :
    restrictAssignment (G := G) hT a = Reindex hST s ↔
      restrictAssignment (G := G) hS a = s := by
  constructor
  · intro h
    have h1 := congrArg (Reindex (fun n => (hST n).symm)) h
    have h2 : Reindex (fun n => (hST n).symm) (restrictAssignment (G := G) hT a) =
        restrictAssignment (G := G) hS a :=
      reindex_restrictAssignment_eq (G := G) hST hS hT a
    calc
      restrictAssignment (G := G) hS a =
          Reindex (fun n => (hST n).symm) (restrictAssignment (G := G) hT a) := by
            simpa [h2]
      _ = Reindex (fun n => (hST n).symm) (Reindex hST s) := by simpa using h1
      _ = s := reindex_inv (S := S) (T := T) hST s
  · intro h
    have h1 := congrArg (Reindex hST) h
    have h2 : Reindex hST (restrictAssignment (G := G) hS a) =
        restrictAssignment (G := G) hT a := by
      simpa using
        (reindex_restrictAssignment_eq (G := G)
          (hST := fun n => (hST n).symm) (hS := hT) (hT := hS) a)
    calc
      restrictAssignment (G := G) hT a = Reindex hST (restrictAssignment (G := G) hS a) := h2.symm
      _ = Reindex hST s := by simpa [h]

/-!
Audit bridge for unclosed assumptions in the d-separation ↔ CI layer.

This file intentionally contains the remaining axioms that are known and
tracked. `MarkovGenerator` re-exports them as theorems so downstream bridges
do not depend on raw `axiom` declarations.
-/



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

private theorem marginalMass_reindex
    {S T : Finset ℕ}
    (hST : ∀ n, n ∈ S ↔ n ∈ T)
    (hS : S ⊆ G.nodes) (hT : T ⊆ G.nodes)
    (P : FinitePMF (Assignment G Var))
    (s : AssignOn Var S) :
    marginalMass P T hT (Reindex hST s) = marginalMass P S hS s := by
  unfold marginalMass
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases h : restrictAssignment (G := G) hT a = Reindex hST s
  · have h' := (restrict_assign_eq_iff (G := G) (Var := Var) hST hS hT a s).1 h
    simp [h, h']
  · have h' : ¬ restrictAssignment (G := G) hS a = s := by
      intro hs
      exact h ((restrict_assign_eq_iff (G := G) (Var := Var) hST hS hT a s).2 hs)
    simp [h, h']

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

/--
Public node-set algebraic CI with an explicit graph-domain witness.

The previous `∀ hnodes, ...` shape made statements with out-of-graph variables
vacuously true.  This proof-carrying form records that the queried node set is
actually contained in the DAG before exposing the algebraic CI fact.
-/
def CIAlgOnNodes (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) : Prop :=
  ∃ hnodes : X ∪ Y ∪ Z ⊆ G.nodes, CIAlg P X Y Z hnodes

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

private def tuple3Z {α β γ : Type} (b : β) :
    AssignOn (Tuple3Var α β γ) ({1} : Finset ℕ) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ _ =>
          simp at hn

private def tuple3XYZ {α β γ : Type} (a : α) (b : β) (c : γ) :
    AssignOn (Tuple3Var α β γ) (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ)) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        exact a
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ n =>
          cases n with
          | zero =>
            exact c
          | succ _ =>
            simp at hn

private def tuple3XZ {α β γ : Type} (a : α) (b : β) :
    AssignOn (Tuple3Var α β γ) (({0} : Finset ℕ) ∪ ({1} : Finset ℕ)) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        exact a
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ _ =>
          simp at hn

private def tuple3YZ {α β γ : Type} (b : β) (c : γ) :
    AssignOn (Tuple3Var α β γ) (({2} : Finset ℕ) ∪ ({1} : Finset ℕ)) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ n =>
          cases n with
          | zero =>
            exact c
          | succ _ =>
            simp at hn

private theorem restrict_eq_tuple3XYZ_iff {G : DAG} {α β γ : Type}
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes)
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple3Var α β γ)) (a : α) (b : β) (c : γ) :
    restrictAssignment hnodes x = tuple3XYZ a b c ↔
      x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c := by
  constructor
  · intro h
    constructor
    · have := congrFun h ⟨0, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple3XYZ, Tuple3Var] using this
    · constructor
      · have := congrFun h ⟨1, by simp⟩
        simpa [restrictAssignment, restrictAssign, tuple3XYZ, Tuple3Var] using this
      · have := congrFun h ⟨2, by simp⟩
        simpa [restrictAssignment, restrictAssign, tuple3XYZ, Tuple3Var] using this
  · rintro ⟨hA, hB, hC⟩
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simpa [restrictAssignment, restrictAssign, tuple3XYZ, Tuple3Var] using hA
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple3XYZ, Tuple3Var] using hB
        | succ n =>
          cases n with
          | zero =>
            simpa [restrictAssignment, restrictAssign, tuple3XYZ, Tuple3Var] using hC
          | succ _ =>
            simp at hn

private theorem restrict_eq_tuple3Z_iff {G : DAG} {α β γ : Type}
    (h1 : 1 ∈ G.nodes)
    (hZ : ({1} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple3Var α β γ)) (b : β) :
    restrictAssignment hZ x = tuple3Z b ↔ x ⟨1, h1⟩ = b := by
  constructor
  · intro h
    have := congrFun h ⟨1, by simp⟩
    simpa [restrictAssignment, restrictAssign, tuple3Z, Tuple3Var] using this
  · intro hB
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple3Z, Tuple3Var] using hB
        | succ _ =>
          simp at hn

private theorem restrict_eq_tuple3XZ_iff {G : DAG} {α β γ : Type}
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (hXZ : ({0} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple3Var α β γ)) (a : α) (b : β) :
    restrictAssignment hXZ x = tuple3XZ a b ↔
      x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b := by
  constructor
  · intro h
    constructor
    · have := congrFun h ⟨0, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple3XZ, Tuple3Var] using this
    · have := congrFun h ⟨1, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple3XZ, Tuple3Var] using this
  · rintro ⟨hA, hB⟩
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simpa [restrictAssignment, restrictAssign, tuple3XZ, Tuple3Var] using hA
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple3XZ, Tuple3Var] using hB
        | succ _ =>
          simp at hn

private theorem restrict_eq_tuple3YZ_iff {G : DAG} {α β γ : Type}
    (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes)
    (hYZ : ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple3Var α β γ)) (b : β) (c : γ) :
    restrictAssignment hYZ x = tuple3YZ b c ↔
      x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c := by
  constructor
  · intro h
    constructor
    · have := congrFun h ⟨1, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple3YZ, Tuple3Var] using this
    · have := congrFun h ⟨2, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple3YZ, Tuple3Var] using this
  · rintro ⟨hB, hC⟩
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple3YZ, Tuple3Var] using hB
        | succ n =>
          cases n with
          | zero =>
            simpa [restrictAssignment, restrictAssign, tuple3YZ, Tuple3Var] using hC
          | succ _ =>
            simp at hn

private theorem tuple3XYZ_restrict_Z {α β γ : Type} (a : α) (b : β) (c : γ) :
    restrictAssign
        (subset_Z_of_XYZ ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
        (tuple3XYZ a b c) =
      tuple3Z b := by
  ext i
  cases i with
  | mk n hn =>
    cases n with
    | zero =>
      simp at hn
    | succ n =>
      cases n with
      | zero =>
        rfl
      | succ _ =>
        simp at hn

private theorem tuple3XYZ_restrict_XZ {α β γ : Type} (a : α) (b : β) (c : γ) :
    restrictAssign
        (subset_XZ_of_XYZ ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
        (tuple3XYZ a b c) =
      tuple3XZ a b := by
  ext i
  cases i with
  | mk n hn =>
    cases n with
    | zero =>
      rfl
    | succ n =>
      cases n with
      | zero =>
        rfl
      | succ _ =>
        simp at hn

private theorem tuple3XYZ_restrict_YZ {α β γ : Type} (a : α) (b : β) (c : γ) :
    restrictAssign
        (subset_YZ_of_XYZ ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ))
        (tuple3XYZ a b c) =
      tuple3YZ b c := by
  ext i
  cases i with
  | mk n hn =>
    cases n with
    | zero =>
      simp at hn
    | succ n =>
      cases n with
      | zero =>
        rfl
      | succ n =>
        cases n with
        | zero =>
          rfl
        | succ _ =>
          simp at hn

private theorem project3_pmf_eq_marginalXYZ {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes)
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (a : α) (b : β) (c : γ) :
    (project3PMF M h0 h1 h2).pmf (a, b, c) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ))
        hnodes (tuple3XYZ a b c) := by
  unfold project3PMF FinitePMF.map marginalMass
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c
  · have hr : restrictAssignment hnodes x = tuple3XYZ a b c :=
      (restrict_eq_tuple3XYZ_iff h0 h1 h2 hnodes x a b c).2 h
    have ht : (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c) := by
      rcases h with ⟨hA, hB, hC⟩
      change (x ⟨0, h0⟩, x ⟨1, h1⟩, x ⟨2, h2⟩) = (a, b, c)
      rw [hA, hB, hC]
      rfl
    calc
      (if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c) then
          M.P.pmf x else 0) = M.P.pmf x := if_pos ht
      _ = (if restrictAssignment hnodes x = tuple3XYZ a b c then M.P.pmf x else 0) :=
          (if_pos hr).symm
  · have hr : restrictAssignment hnodes x ≠ tuple3XYZ a b c := by
      intro hr
      exact h ((restrict_eq_tuple3XYZ_iff h0 h1 h2 hnodes x a b c).1 hr)
    have ht : ¬ (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c) := by
      intro ht
      apply h
      constructor
      · exact congrArg Prod.fst ht
      · constructor
        · exact congrArg Prod.fst (congrArg Prod.snd ht)
        · exact congrArg Prod.snd (congrArg Prod.snd ht)
    calc
      (if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c) then
          M.P.pmf x else 0) = 0 := if_neg ht
      _ = (if restrictAssignment hnodes x = tuple3XYZ a b c then M.P.pmf x else 0) :=
          (if_neg hr).symm

private theorem project3_context_b_eq_marginalZ {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes)
    (hZ : ({1} : Finset ℕ) ⊆ G.nodes)
    (b : β) :
    (∑ a' : α, ∑ c' : γ, (project3PMF M h0 h1 h2).pmf (a', b, c')) =
      marginalMass M.P ({1} : Finset ℕ) hZ (tuple3Z b) := by
  unfold project3PMF FinitePMF.map marginalMass
  calc
    (∑ a' : α, ∑ c' : γ,
        ∑ x : Assignment G (Tuple3Var α β γ),
          if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
            M.P.pmf x
          else 0)
        = ∑ a' : α, ∑ x : Assignment G (Tuple3Var α β γ), ∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
                M.P.pmf x
              else 0 := by
      apply Finset.sum_congr rfl
      intro a' ha'
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple3Var α β γ),
            ∑ a' : α, ∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
                M.P.pmf x
              else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple3Var α β γ),
          if restrictAssignment hZ x = tuple3Z b then M.P.pmf x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hb : x ⟨1, h1⟩ = b
      · have hr : restrictAssignment hZ x = tuple3Z b :=
          (restrict_eq_tuple3Z_iff h1 hZ x b).2 hb
        have hinner :
            (∑ a' : α, ∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
                M.P.pmf x
              else 0) = M.P.pmf x := by
          calc
            (∑ a' : α, ∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
                M.P.pmf x
              else 0)
                = ∑ q : α × γ,
                    if (x ⟨0, h0⟩, x ⟨2, h2⟩) = q then M.P.pmf x else 0 := by
              rw [← Finset.sum_product' (s := (Finset.univ : Finset α))
                (t := (Finset.univ : Finset γ))]
              simp [hb, Prod.ext_iff]
            _ = M.P.pmf x := by
              exact
                (Fintype.sum_ite_eq
                  (i := (x ⟨0, h0⟩, x ⟨2, h2⟩))
                  (f := fun _ : α × γ => M.P.pmf x))
        calc
          (∑ a' : α, ∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
                M.P.pmf x
              else 0) = M.P.pmf x := hinner
          _ = (if restrictAssignment hZ x = tuple3Z b then M.P.pmf x else 0) :=
            (if_pos hr).symm
      · have hr : restrictAssignment hZ x ≠ tuple3Z b := by
          intro hr
          exact hb ((restrict_eq_tuple3Z_iff h1 hZ x b).1 hr)
        have hinner :
            (∑ a' : α, ∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
                M.P.pmf x
              else 0) = 0 := by
          simp [Prod.ext_iff, hb]
        calc
          (∑ a' : α, ∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c') then
                M.P.pmf x
              else 0) = 0 := hinner
          _ = (if restrictAssignment hZ x = tuple3Z b then M.P.pmf x else 0) :=
            (if_neg hr).symm

private theorem project3_sum_c_eq_marginalXZ {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes)
    (hXZ : ({0} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (a : α) (b : β) :
    (∑ c' : γ, (project3PMF M h0 h1 h2).pmf (a, b, c')) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({1} : Finset ℕ)) hXZ (tuple3XZ a b) := by
  unfold project3PMF FinitePMF.map marginalMass
  calc
    (∑ c' : γ, ∑ x : Assignment G (Tuple3Var α β γ),
        if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') then
          M.P.pmf x
        else 0)
        = ∑ x : Assignment G (Tuple3Var α β γ), ∑ c' : γ,
            if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') then
              M.P.pmf x
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple3Var α β γ),
          if restrictAssignment hXZ x = tuple3XZ a b then M.P.pmf x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hab : x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b
      · have hr : restrictAssignment hXZ x = tuple3XZ a b :=
          (restrict_eq_tuple3XZ_iff h0 h1 hXZ x a b).2 hab
        have hinner :
            (∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') then
                M.P.pmf x
              else 0) = M.P.pmf x := by
          rcases hab with ⟨hA, hB⟩
          calc
            (∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') then
                M.P.pmf x
              else 0)
                = ∑ c' : γ, if x ⟨2, h2⟩ = c' then M.P.pmf x else 0 := by
              apply Finset.sum_congr rfl
              intro c' hc'
              by_cases hC : x ⟨2, h2⟩ = c'
              · have ht : (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') := by
                  change (x ⟨0, h0⟩, x ⟨1, h1⟩, x ⟨2, h2⟩) = (a, b, c')
                  rw [hA, hB, hC]
                  rfl
                rw [if_pos ht, if_pos hC]
              · have ht : ¬ (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') := by
                  intro ht
                  exact hC (congrArg Prod.snd (congrArg Prod.snd ht))
                rw [if_neg ht, if_neg hC]
            _ = M.P.pmf x := by
              exact
                (Fintype.sum_ite_eq
                  (i := x ⟨2, h2⟩)
                  (f := fun _ : γ => M.P.pmf x))
        calc
          (∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') then
                M.P.pmf x
              else 0) = M.P.pmf x := hinner
          _ = (if restrictAssignment hXZ x = tuple3XZ a b then M.P.pmf x else 0) :=
            (if_pos hr).symm
      · have hr : restrictAssignment hXZ x ≠ tuple3XZ a b := by
          intro hr
          exact hab ((restrict_eq_tuple3XZ_iff h0 h1 hXZ x a b).1 hr)
        have hinner :
            (∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') then
                M.P.pmf x
              else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro c' hc'
          rw [if_neg]
          intro ht
          apply hab
          constructor
          · exact congrArg Prod.fst ht
          · exact congrArg Prod.fst (congrArg Prod.snd ht)
        calc
          (∑ c' : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a, b, c') then
                M.P.pmf x
              else 0) = 0 := hinner
          _ = (if restrictAssignment hXZ x = tuple3XZ a b then M.P.pmf x else 0) :=
            (if_neg hr).symm

private theorem project3_sum_a_eq_marginalYZ {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes)
    (hYZ : ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (b : β) (c : γ) :
    (∑ a' : α, (project3PMF M h0 h1 h2).pmf (a', b, c)) =
      marginalMass M.P (({2} : Finset ℕ) ∪ ({1} : Finset ℕ)) hYZ (tuple3YZ b c) := by
  unfold project3PMF FinitePMF.map marginalMass
  calc
    (∑ a' : α, ∑ x : Assignment G (Tuple3Var α β γ),
        if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) then
          M.P.pmf x
        else 0)
        = ∑ x : Assignment G (Tuple3Var α β γ), ∑ a' : α,
            if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) then
              M.P.pmf x
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple3Var α β γ),
          if restrictAssignment hYZ x = tuple3YZ b c then M.P.pmf x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hbc : x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c
      · have hr : restrictAssignment hYZ x = tuple3YZ b c :=
          (restrict_eq_tuple3YZ_iff h1 h2 hYZ x b c).2 hbc
        have hinner :
            (∑ a' : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) then
                M.P.pmf x
              else 0) = M.P.pmf x := by
          rcases hbc with ⟨hB, hC⟩
          calc
            (∑ a' : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) then
                M.P.pmf x
              else 0)
                = ∑ a' : α, if x ⟨0, h0⟩ = a' then M.P.pmf x else 0 := by
              apply Finset.sum_congr rfl
              intro a' ha'
              by_cases hA : x ⟨0, h0⟩ = a'
              · have ht : (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) := by
                  change (x ⟨0, h0⟩, x ⟨1, h1⟩, x ⟨2, h2⟩) = (a', b, c)
                  rw [hA, hB, hC]
                  rfl
                rw [if_pos ht, if_pos hA]
              · have ht : ¬ (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) := by
                  intro ht
                  exact hA (congrArg Prod.fst ht)
                rw [if_neg ht, if_neg hA]
            _ = M.P.pmf x := by
              exact
                (Fintype.sum_ite_eq
                  (i := x ⟨0, h0⟩)
                  (f := fun _ : α => M.P.pmf x))
        calc
          (∑ a' : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) then
                M.P.pmf x
              else 0) = M.P.pmf x := hinner
          _ = (if restrictAssignment hYZ x = tuple3YZ b c then M.P.pmf x else 0) :=
            (if_pos hr).symm
      · have hr : restrictAssignment hYZ x ≠ tuple3YZ b c := by
          intro hr
          exact hbc ((restrict_eq_tuple3YZ_iff h1 h2 hYZ x b c).1 hr)
        have hinner :
            (∑ a' : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) then
                M.P.pmf x
              else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro a' ha'
          rw [if_neg]
          intro ht
          apply hbc
          constructor
          · exact congrArg Prod.fst (congrArg Prod.snd ht)
          · exact congrArg Prod.snd (congrArg Prod.snd ht)
        calc
          (∑ a' : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩)) x = (a', b, c) then
                M.P.pmf x
              else 0) = 0 := hinner
          _ = (if restrictAssignment hYZ x = tuple3YZ b c then M.P.pmf x else 0) :=
            (if_neg hr).symm

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

private def tuple4Z {α β γ δ : Type} (b : β) (d : δ) :
    AssignOn (Tuple4Var α β γ δ) ({1, 3} : Finset ℕ) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ n =>
          cases n with
          | zero =>
            simp at hn
          | succ n =>
            cases n with
            | zero =>
              exact d
            | succ _ =>
              simp at hn

private def tuple4XYZ {α β γ δ : Type} (a : α) (b : β) (c : γ) (d : δ) :
    AssignOn (Tuple4Var α β γ δ)
      (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        exact a
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ n =>
          cases n with
          | zero =>
            exact c
          | succ n =>
            cases n with
            | zero =>
              exact d
            | succ _ =>
              simp at hn

private def tuple4XZ {α β γ δ : Type} (a : α) (b : β) (d : δ) :
    AssignOn (Tuple4Var α β γ δ) (({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        exact a
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ n =>
          cases n with
          | zero =>
            simp at hn
          | succ n =>
            cases n with
            | zero =>
              exact d
            | succ _ =>
              simp at hn

private def tuple4YZ {α β γ δ : Type} (b : β) (c : γ) (d : δ) :
    AssignOn (Tuple4Var α β γ δ) (({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)) :=
  fun i => by
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          exact b
        | succ n =>
          cases n with
          | zero =>
            exact c
          | succ n =>
            cases n with
            | zero =>
              exact d
            | succ _ =>
              simp at hn

private theorem restrict_eq_tuple4XYZ_iff {G : DAG} {α β γ δ : Type}
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple4Var α β γ δ)) (a : α) (b : β) (c : γ) (d : δ) :
    restrictAssignment hnodes x = tuple4XYZ a b c d ↔
      x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c ∧ x ⟨3, h3⟩ = d := by
  constructor
  · intro h
    constructor
    · have := congrFun h ⟨0, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using this
    · constructor
      · have := congrFun h ⟨1, by simp⟩
        simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using this
      · constructor
        · have := congrFun h ⟨2, by simp⟩
          simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using this
        · have := congrFun h ⟨3, by simp⟩
          simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using this
  · rintro ⟨hA, hB, hC, hD⟩
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using hA
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using hB
        | succ n =>
          cases n with
          | zero =>
            simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using hC
          | succ n =>
            cases n with
            | zero =>
              simpa [restrictAssignment, restrictAssign, tuple4XYZ, Tuple4Var] using hD
            | succ _ =>
              simp at hn

private theorem restrict_eq_tuple4Z_iff {G : DAG} {α β γ δ : Type}
    (h1 : 1 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hZ : ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple4Var α β γ δ)) (b : β) (d : δ) :
    restrictAssignment hZ x = tuple4Z b d ↔
      x ⟨1, h1⟩ = b ∧ x ⟨3, h3⟩ = d := by
  constructor
  · intro h
    constructor
    · have := congrFun h ⟨1, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple4Z, Tuple4Var] using this
    · have := congrFun h ⟨3, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple4Z, Tuple4Var] using this
  · rintro ⟨hB, hD⟩
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple4Z, Tuple4Var] using hB
        | succ n =>
          cases n with
          | zero =>
            simp at hn
          | succ n =>
            cases n with
            | zero =>
              simpa [restrictAssignment, restrictAssign, tuple4Z, Tuple4Var] using hD
            | succ _ =>
              simp at hn

private theorem restrict_eq_tuple4XZ_iff {G : DAG} {α β γ δ : Type}
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hXZ : ({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple4Var α β γ δ)) (a : α) (b : β) (d : δ) :
    restrictAssignment hXZ x = tuple4XZ a b d ↔
      x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b ∧ x ⟨3, h3⟩ = d := by
  constructor
  · intro h
    constructor
    · have := congrFun h ⟨0, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple4XZ, Tuple4Var] using this
    · constructor
      · have := congrFun h ⟨1, by simp⟩
        simpa [restrictAssignment, restrictAssign, tuple4XZ, Tuple4Var] using this
      · have := congrFun h ⟨3, by simp⟩
        simpa [restrictAssignment, restrictAssign, tuple4XZ, Tuple4Var] using this
  · rintro ⟨hA, hB, hD⟩
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simpa [restrictAssignment, restrictAssign, tuple4XZ, Tuple4Var] using hA
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple4XZ, Tuple4Var] using hB
        | succ n =>
          cases n with
          | zero =>
            simp at hn
          | succ n =>
            cases n with
            | zero =>
              simpa [restrictAssignment, restrictAssign, tuple4XZ, Tuple4Var] using hD
            | succ _ =>
              simp at hn

private theorem restrict_eq_tuple4YZ_iff {G : DAG} {α β γ δ : Type}
    (h1 : 1 ∈ G.nodes) (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hYZ : ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (x : Assignment G (Tuple4Var α β γ δ)) (b : β) (c : γ) (d : δ) :
    restrictAssignment hYZ x = tuple4YZ b c d ↔
      x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c ∧ x ⟨3, h3⟩ = d := by
  constructor
  · intro h
    constructor
    · have := congrFun h ⟨1, by simp⟩
      simpa [restrictAssignment, restrictAssign, tuple4YZ, Tuple4Var] using this
    · constructor
      · have := congrFun h ⟨2, by simp⟩
        simpa [restrictAssignment, restrictAssign, tuple4YZ, Tuple4Var] using this
      · have := congrFun h ⟨3, by simp⟩
        simpa [restrictAssignment, restrictAssign, tuple4YZ, Tuple4Var] using this
  · rintro ⟨hB, hC, hD⟩
    ext i
    cases i with
    | mk n hn =>
      cases n with
      | zero =>
        simp at hn
      | succ n =>
        cases n with
        | zero =>
          simpa [restrictAssignment, restrictAssign, tuple4YZ, Tuple4Var] using hB
        | succ n =>
          cases n with
          | zero =>
            simpa [restrictAssignment, restrictAssign, tuple4YZ, Tuple4Var] using hC
          | succ n =>
            cases n with
            | zero =>
              simpa [restrictAssignment, restrictAssign, tuple4YZ, Tuple4Var] using hD
            | succ _ =>
              simp at hn

private theorem tuple4XYZ_restrict_Z {α β γ δ : Type}
    (a : α) (b : β) (c : γ) (d : δ) :
    restrictAssign
        (subset_Z_of_XYZ ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ))
        (tuple4XYZ a b c d) =
      tuple4Z b d := by
  ext i
  cases i with
  | mk n hn =>
    cases n with
    | zero =>
      simp at hn
    | succ n =>
      cases n with
      | zero =>
        rfl
      | succ n =>
        cases n with
        | zero =>
          simp at hn
        | succ n =>
          cases n with
          | zero =>
            rfl
          | succ _ =>
            simp at hn

private theorem tuple4XYZ_restrict_XZ {α β γ δ : Type}
    (a : α) (b : β) (c : γ) (d : δ) :
    restrictAssign
        (subset_XZ_of_XYZ ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ))
        (tuple4XYZ a b c d) =
      tuple4XZ a b d := by
  ext i
  cases i with
  | mk n hn =>
    cases n with
    | zero =>
      rfl
    | succ n =>
      cases n with
      | zero =>
        rfl
      | succ n =>
        cases n with
        | zero =>
          simp at hn
        | succ n =>
          cases n with
          | zero =>
            rfl
          | succ _ =>
            simp at hn

private theorem tuple4XYZ_restrict_YZ {α β γ δ : Type}
    (a : α) (b : β) (c : γ) (d : δ) :
    restrictAssign
        (subset_YZ_of_XYZ ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ))
        (tuple4XYZ a b c d) =
      tuple4YZ b c d := by
  ext i
  cases i with
  | mk n hn =>
    cases n with
    | zero =>
      simp at hn
    | succ n =>
      cases n with
      | zero =>
        rfl
      | succ n =>
        cases n with
        | zero =>
          rfl
        | succ n =>
          cases n with
          | zero =>
            rfl
          | succ _ =>
            simp at hn

private theorem project4_pmf_eq_marginalXYZ {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (a : α) (b : β) (c : γ) (d : δ) :
    (project4PMF M h0 h1 h2 h3).pmf (a, b, c, d) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ))
        hnodes (tuple4XYZ a b c d) := by
  unfold project4PMF FinitePMF.map marginalMass
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c ∧ x ⟨3, h3⟩ = d
  · have hr : restrictAssignment hnodes x = tuple4XYZ a b c d :=
      (restrict_eq_tuple4XYZ_iff h0 h1 h2 h3 hnodes x a b c d).2 h
    have ht : (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
        (a, b, c, d) := by
      rcases h with ⟨hA, hB, hC, hD⟩
      change (x ⟨0, h0⟩, x ⟨1, h1⟩, x ⟨2, h2⟩, x ⟨3, h3⟩) = (a, b, c, d)
      rw [hA, hB, hC, hD]
      rfl
    calc
      (if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x = (a, b, c, d) then
          M.P.pmf x else 0) = M.P.pmf x := if_pos ht
      _ = (if restrictAssignment hnodes x = tuple4XYZ a b c d then M.P.pmf x else 0) :=
          (if_pos hr).symm
  · have hr : restrictAssignment hnodes x ≠ tuple4XYZ a b c d := by
      intro hr
      exact h ((restrict_eq_tuple4XYZ_iff h0 h1 h2 h3 hnodes x a b c d).1 hr)
    have ht : ¬ (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
        (a, b, c, d) := by
      intro ht
      apply h
      constructor
      · exact congrArg Prod.fst ht
      · constructor
        · exact congrArg Prod.fst (congrArg Prod.snd ht)
        · constructor
          · exact congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd ht))
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd ht))
    calc
      (if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x = (a, b, c, d) then
          M.P.pmf x else 0) = 0 := if_neg ht
      _ = (if restrictAssignment hnodes x = tuple4XYZ a b c d then M.P.pmf x else 0) :=
          (if_neg hr).symm

private theorem project4_context_bd_eq_marginalZ {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hZ : ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (b : β) (d : δ) :
    marginalYWMass (project4PMF M h0 h1 h2 h3) (b, d) =
      marginalMass M.P ({1, 3} : Finset ℕ) hZ (tuple4Z b d) := by
  unfold marginalYWMass project4PMF FinitePMF.map marginalMass
  calc
    (∑ x0 : α, ∑ z0 : γ,
        ∑ x : Assignment G (Tuple4Var α β γ δ),
          if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
              (x0, b, z0, d) then M.P.pmf x else 0)
        = ∑ x0 : α, ∑ x : Assignment G (Tuple4Var α β γ δ), ∑ z0 : γ,
            if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                (x0, b, z0, d) then M.P.pmf x else 0 := by
      apply Finset.sum_congr rfl
      intro x0 hx0
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple4Var α β γ δ), ∑ x0 : α, ∑ z0 : γ,
            if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                (x0, b, z0, d) then M.P.pmf x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple4Var α β γ δ),
          if restrictAssignment hZ x = tuple4Z b d then M.P.pmf x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hbd : x ⟨1, h1⟩ = b ∧ x ⟨3, h3⟩ = d
      · have hr : restrictAssignment hZ x = tuple4Z b d :=
          (restrict_eq_tuple4Z_iff h1 h3 hZ x b d).2 hbd
        rcases hbd with ⟨hB, hD⟩
        have hinner :
            (∑ x0 : α, ∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, z0, d) then M.P.pmf x else 0) = M.P.pmf x := by
          calc
            (∑ x0 : α, ∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, z0, d) then M.P.pmf x else 0)
                = ∑ q : α × γ,
                    if (x ⟨0, h0⟩, x ⟨2, h2⟩) = q then M.P.pmf x else 0 := by
              rw [← Finset.sum_product' (s := (Finset.univ : Finset α))
                (t := (Finset.univ : Finset γ))]
              simp [hB, hD, Prod.ext_iff]
            _ = M.P.pmf x := by
              exact
                (Fintype.sum_ite_eq
                  (i := (x ⟨0, h0⟩, x ⟨2, h2⟩))
                  (f := fun _ : α × γ => M.P.pmf x))
        calc
          (∑ x0 : α, ∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, z0, d) then M.P.pmf x else 0) = M.P.pmf x := hinner
          _ = (if restrictAssignment hZ x = tuple4Z b d then M.P.pmf x else 0) :=
            (if_pos hr).symm
      · have hr : restrictAssignment hZ x ≠ tuple4Z b d := by
          intro hr
          exact hbd ((restrict_eq_tuple4Z_iff h1 h3 hZ x b d).1 hr)
        have hinner :
            (∑ x0 : α, ∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, z0, d) then M.P.pmf x else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro x0 hx0
          apply Finset.sum_eq_zero
          intro z0 hz0
          rw [if_neg]
          intro ht
          apply hbd
          constructor
          · exact congrArg Prod.fst (congrArg Prod.snd ht)
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd ht))
        calc
          (∑ x0 : α, ∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, z0, d) then M.P.pmf x else 0) = 0 := hinner
          _ = (if restrictAssignment hZ x = tuple4Z b d then M.P.pmf x else 0) :=
            (if_neg hr).symm

private theorem project4_sum_c_eq_marginalXZ {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hXZ : ({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (a : α) (b : β) (d : δ) :
    marginalXYWMass (project4PMF M h0 h1 h2 h3) (a, b, d) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)) hXZ (tuple4XZ a b d) := by
  unfold marginalXYWMass project4PMF FinitePMF.map marginalMass
  calc
    (∑ z0 : γ, ∑ x : Assignment G (Tuple4Var α β γ δ),
        if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
            (a, b, z0, d) then M.P.pmf x else 0)
        = ∑ x : Assignment G (Tuple4Var α β γ δ), ∑ z0 : γ,
            if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                (a, b, z0, d) then M.P.pmf x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple4Var α β γ δ),
          if restrictAssignment hXZ x = tuple4XZ a b d then M.P.pmf x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases habd : x ⟨0, h0⟩ = a ∧ x ⟨1, h1⟩ = b ∧ x ⟨3, h3⟩ = d
      · have hr : restrictAssignment hXZ x = tuple4XZ a b d :=
          (restrict_eq_tuple4XZ_iff h0 h1 h3 hXZ x a b d).2 habd
        rcases habd with ⟨hA, hB, hD⟩
        have hinner :
            (∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (a, b, z0, d) then M.P.pmf x else 0) = M.P.pmf x := by
          calc
            (∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (a, b, z0, d) then M.P.pmf x else 0)
                = ∑ z0 : γ, if x ⟨2, h2⟩ = z0 then M.P.pmf x else 0 := by
              apply Finset.sum_congr rfl
              intro z0 hz0
              by_cases hC : x ⟨2, h2⟩ = z0
              · have ht : (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                    (a, b, z0, d) := by
                  change (x ⟨0, h0⟩, x ⟨1, h1⟩, x ⟨2, h2⟩, x ⟨3, h3⟩) = (a, b, z0, d)
                  rw [hA, hB, hC, hD]
                  rfl
                rw [if_pos ht, if_pos hC]
              · have ht : ¬ (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                    (a, b, z0, d) := by
                  intro ht
                  exact hC (congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd ht)))
                rw [if_neg ht, if_neg hC]
            _ = M.P.pmf x := by
              exact
                (Fintype.sum_ite_eq
                  (i := x ⟨2, h2⟩)
                  (f := fun _ : γ => M.P.pmf x))
        calc
          (∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (a, b, z0, d) then M.P.pmf x else 0) = M.P.pmf x := hinner
          _ = (if restrictAssignment hXZ x = tuple4XZ a b d then M.P.pmf x else 0) :=
            (if_pos hr).symm
      · have hr : restrictAssignment hXZ x ≠ tuple4XZ a b d := by
          intro hr
          exact habd ((restrict_eq_tuple4XZ_iff h0 h1 h3 hXZ x a b d).1 hr)
        have hinner :
            (∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (a, b, z0, d) then M.P.pmf x else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro z0 hz0
          rw [if_neg]
          intro ht
          apply habd
          constructor
          · exact congrArg Prod.fst ht
          · constructor
            · exact congrArg Prod.fst (congrArg Prod.snd ht)
            · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd ht))
        calc
          (∑ z0 : γ,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (a, b, z0, d) then M.P.pmf x else 0) = 0 := hinner
          _ = (if restrictAssignment hXZ x = tuple4XZ a b d then M.P.pmf x else 0) :=
            (if_neg hr).symm

private theorem project4_sum_a_eq_marginalYZ {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (h0 : 0 ∈ G.nodes) (h1 : 1 ∈ G.nodes)
    (h2 : 2 ∈ G.nodes) (h3 : 3 ∈ G.nodes)
    (hYZ : ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (b : β) (c : γ) (d : δ) :
    marginalYZWMass (project4PMF M h0 h1 h2 h3) (b, c, d) =
      marginalMass M.P (({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)) hYZ (tuple4YZ b c d) := by
  unfold marginalYZWMass project4PMF FinitePMF.map marginalMass
  calc
    (∑ x0 : α, ∑ x : Assignment G (Tuple4Var α β γ δ),
        if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
            (x0, b, c, d) then M.P.pmf x else 0)
        = ∑ x : Assignment G (Tuple4Var α β γ δ), ∑ x0 : α,
            if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                (x0, b, c, d) then M.P.pmf x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Assignment G (Tuple4Var α β γ δ),
          if restrictAssignment hYZ x = tuple4YZ b c d then M.P.pmf x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hbcd : x ⟨1, h1⟩ = b ∧ x ⟨2, h2⟩ = c ∧ x ⟨3, h3⟩ = d
      · have hr : restrictAssignment hYZ x = tuple4YZ b c d :=
          (restrict_eq_tuple4YZ_iff h1 h2 h3 hYZ x b c d).2 hbcd
        rcases hbcd with ⟨hB, hC, hD⟩
        have hinner :
            (∑ x0 : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, c, d) then M.P.pmf x else 0) = M.P.pmf x := by
          calc
            (∑ x0 : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, c, d) then M.P.pmf x else 0)
                = ∑ x0 : α, if x ⟨0, h0⟩ = x0 then M.P.pmf x else 0 := by
              apply Finset.sum_congr rfl
              intro x0 hx0
              by_cases hA : x ⟨0, h0⟩ = x0
              · have ht : (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                    (x0, b, c, d) := by
                  change (x ⟨0, h0⟩, x ⟨1, h1⟩, x ⟨2, h2⟩, x ⟨3, h3⟩) = (x0, b, c, d)
                  rw [hA, hB, hC, hD]
                  rfl
                rw [if_pos ht, if_pos hA]
              · have ht : ¬ (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                    (x0, b, c, d) := by
                  intro ht
                  exact hA (congrArg Prod.fst ht)
                rw [if_neg ht, if_neg hA]
            _ = M.P.pmf x := by
              exact
                (Fintype.sum_ite_eq
                  (i := x ⟨0, h0⟩)
                  (f := fun _ : α => M.P.pmf x))
        calc
          (∑ x0 : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, c, d) then M.P.pmf x else 0) = M.P.pmf x := hinner
          _ = (if restrictAssignment hYZ x = tuple4YZ b c d then M.P.pmf x else 0) :=
            (if_pos hr).symm
      · have hr : restrictAssignment hYZ x ≠ tuple4YZ b c d := by
          intro hr
          exact hbcd ((restrict_eq_tuple4YZ_iff h1 h2 h3 hYZ x b c d).1 hr)
        have hinner :
            (∑ x0 : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, c, d) then M.P.pmf x else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro x0 hx0
          rw [if_neg]
          intro ht
          apply hbcd
          constructor
          · exact congrArg Prod.fst (congrArg Prod.snd ht)
          · constructor
            · exact congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd ht))
            · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd ht))
        calc
          (∑ x0 : α,
              if (fun a => (a ⟨0, h0⟩, a ⟨1, h1⟩, a ⟨2, h2⟩, a ⟨3, h3⟩)) x =
                  (x0, b, c, d) then M.P.pmf x else 0) = 0 := hinner
          _ = (if restrictAssignment hYZ x = tuple4YZ b c d then M.P.pmf x else 0) :=
            (if_neg hr).symm

-- Keep the variable context for unsafe axioms aligned with `MarkovGenerator` APIs.
variable {G : DAG} {Var : ℕ → Type}
variable [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)]

-- Context-mass positivity is proved by extending any witness assignment to S.
theorem contextMass_pos_of_strictlyPositive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (S : Finset ℕ) (hnodes : S ⊆ G.nodes) (s : AssignOn Var S) :
    0 < contextMass P S hnodes s := by
  classical
  let hne : ∃ ω : Assignment G Var, P.pmf ω ≠ 0 := by
    by_contra h
    have hall_zero : ∀ ω : Assignment G Var, P.pmf ω = 0 := by
      intro ω
      by_contra hω
      exact h ⟨ω, hω⟩
    have hsum : (∑ ω : Assignment G Var, P.pmf ω) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro ω _
      exact hall_zero ω
    have hzero : (1 : ℝ) = 0 := by
      simpa [FinitePMF.sum_one] using hsum
    norm_num at hzero
  let a0 : Assignment G Var := Classical.choose hne
  let a : Assignment G Var := fun v => if hv : v.1 ∈ S then s ⟨v.1, hv⟩ else a0 ⟨v.1, v.2⟩
  have hrestrict : restrictAssignment hnodes a = s := by
    ext t
    have htS : t.1 ∈ S := t.2
    simp [a, restrictAssignment, restrictAssign, htS]
  have hnonneg : ∀ ω : Assignment G Var, 0 ≤ (if restrictAssignment hnodes ω = s then P.pmf ω else 0) := by
    intro ω
    by_cases hω : restrictAssignment hnodes ω = s
    · simp [hω, le_of_lt (hpos ω)]
    · simp [hω]
  have hterm_pos :
      0 < (if restrictAssignment hnodes a = s then P.pmf a else 0) := by
    simp [hrestrict, hpos a]
  have hsum_ge :
      (if restrictAssignment hnodes a = s then P.pmf a else 0) ≤ contextMass P S hnodes s := by
    simpa [contextMass] using
      (Finset.single_le_sum (s := (Finset.univ : Finset (Assignment G Var)))
        (f := fun ω => if restrictAssignment hnodes ω = s then P.pmf ω else 0)
        (by
          intro ω hω
          exact hnonneg ω)
        (by simp))
  exact lt_of_lt_of_le hterm_pos hsum_ge

-- Pending audit entry: `CIExp` ↔ `CIAlg` under positivity.
axiom CIExp_iff_CIAlg_of_positive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) :
    CIExp P X Y Z hnodes ↔ CIAlg P X Y Z hnodes

-- Symmetry of algebraic CI.
theorem ci_symm (P : FinitePMF (Assignment G Var)) {X Y Z : Finset ℕ} :
    CIAlgOnNodes P X Y Z → CIAlgOnNodes P Y X Z := by
  rintro ⟨hnodes, hXY⟩
  let hnodes' : Y ∪ X ∪ Z ⊆ G.nodes := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hnodes
  refine ⟨hnodes', ?_⟩
  let hswapYX : ∀ n, n ∈ Y ∪ X ∪ Z ↔ n ∈ X ∪ Y ∪ Z := by
    intro n
    simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
  intro xyz'
  let xyz : AssignOn Var (X ∪ Y ∪ Z) := Reindex hswapYX xyz'
  have h1 := hXY xyz
  have hmass : marginalMass P (Y ∪ X ∪ Z) hnodes' xyz' =
      marginalMass P (X ∪ Y ∪ Z) hnodes xyz := by
    have htmp : marginalMass P (X ∪ Y ∪ Z) hnodes
        (Reindex hswapYX xyz') = marginalMass P (Y ∪ X ∪ Z) hnodes' xyz' := by
      simpa [Reindex] using
        (marginalMass_reindex (G := G) (Var := Var) (hST := hswapYX)
          (hS := hnodes') (hT := hnodes) P xyz')
    simpa [xyz] using htmp.symm
  have hXZ :
      restrictAssign (subset_XZ_of_XYZ (X := X) (Y := Y) (Z := Z)) xyz =
        restrictAssign (subset_YZ_of_XYZ (X := Y) (Y := X) (Z := Z)) xyz' := by
    ext u
    simpa [xyz] using (reindex_restrict (Var := Var)
      (hST := hswapYX)
      (hSU := subset_YZ_of_XYZ (X := Y) (Y := X) (Z := Z))
      (hTU := subset_XZ_of_XYZ (X := X) (Y := Y) (Z := Z))
      (a := xyz') (u := u))
  have hYZ :
      restrictAssign (subset_YZ_of_XYZ (X := X) (Y := Y) (Z := Z)) xyz =
        restrictAssign (subset_XZ_of_XYZ (X := Y) (Y := X) (Z := Z)) xyz' := by
    ext u
    simpa [xyz] using (reindex_restrict (Var := Var)
      (hST := hswapYX)
      (hSU := subset_XZ_of_XYZ (X := Y) (Y := X) (Z := Z))
      (hTU := subset_YZ_of_XYZ (X := X) (Y := Y) (Z := Z))
      (a := xyz') (u := u))
  have hZ :
      restrictAssign (subset_Z_of_XYZ X Y Z) xyz =
        restrictAssign (subset_Z_of_XYZ Y X Z) xyz' := by
    ext u
    simpa [xyz] using (reindex_restrict (Var := Var)
      (hST := hswapYX)
      (hSU := subset_Z_of_XYZ Y X Z)
      (hTU := subset_Z_of_XYZ X Y Z)
      (a := xyz') (u := u))
  -- Goal-side rearrangement of set unions is handled by `simp`.
  simpa [CIAlg, xyz, hmass, hXZ, hYZ, hZ,
    Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using
    h1.trans (mul_comm _ _)

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

-- Three-variable projection bridge.
theorem isMarkovChain_of_CIExp_project3 {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (hci : CIExp M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ) hnodes) :
    UnsafeIsMarkovChain (project3PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
  intro a b c
  let h0 : 0 ∈ G.nodes := hnodes (by simp)
  let h1 : 1 ∈ G.nodes := hnodes (by simp)
  let h2 : 2 ∈ G.nodes := hnodes (by simp)
  have hAlg :
      CIAlg M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ) hnodes :=
    (CIExp_iff_CIAlg_of_positive M.P M.positive
      ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ) hnodes).1 hci
  have hpoint := hAlg (tuple3XYZ a b c)
  have hpoint' :
      marginalMass M.P (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ))
          hnodes (tuple3XYZ a b c) *
        marginalMass M.P ({1} : Finset ℕ) (subset_Z_of_union hnodes) (tuple3Z b) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({1} : Finset ℕ))
          (subset_XZ_of_union hnodes) (tuple3XZ a b) *
        marginalMass M.P (({2} : Finset ℕ) ∪ ({1} : Finset ℕ))
          (subset_YZ_of_union hnodes) (tuple3YZ b c) := by
    have hZr := tuple3XYZ_restrict_Z (a := a) (b := b) (c := c)
    have hXZr := tuple3XYZ_restrict_XZ (a := a) (b := b) (c := c)
    have hYZr := tuple3XYZ_restrict_YZ (a := a) (b := b) (c := c)
    rw [hZr, hXZr, hYZr] at hpoint
    exact hpoint
  calc
    (project3PMF M h0 h1 h2).pmf (a, b, c) *
        (∑ a' : α, ∑ c' : γ, (project3PMF M h0 h1 h2).pmf (a', b, c')) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ))
          hnodes (tuple3XYZ a b c) *
        marginalMass M.P ({1} : Finset ℕ) (subset_Z_of_union hnodes) (tuple3Z b) := by
        rw [project3_pmf_eq_marginalXYZ M h0 h1 h2 hnodes a b c,
          project3_context_b_eq_marginalZ M h0 h1 h2 (subset_Z_of_union hnodes) b]
    _ =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({1} : Finset ℕ))
          (subset_XZ_of_union hnodes) (tuple3XZ a b) *
        marginalMass M.P (({2} : Finset ℕ) ∪ ({1} : Finset ℕ))
          (subset_YZ_of_union hnodes) (tuple3YZ b c) := hpoint'
    _ =
      (∑ c' : γ, (project3PMF M h0 h1 h2).pmf (a, b, c')) *
        (∑ a' : α, (project3PMF M h0 h1 h2).pmf (a', b, c)) := by
        rw [project3_sum_c_eq_marginalXZ M h0 h1 h2 (subset_XZ_of_union hnodes) a b,
          project3_sum_a_eq_marginalYZ M h0 h1 h2 (subset_YZ_of_union hnodes) b c]


-- Four-variable projection bridge.
theorem condMarkov_of_CIExp_project4 {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (hci : CIExp M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ) hnodes) :
    condMarkov (project4PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
  intro a b c d
  let h0 : 0 ∈ G.nodes := hnodes (by simp)
  let h1 : 1 ∈ G.nodes := hnodes (by simp)
  let h2 : 2 ∈ G.nodes := hnodes (by simp)
  let h3 : 3 ∈ G.nodes := hnodes (by simp)
  have hAlg :
      CIAlg M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ) hnodes :=
    (CIExp_iff_CIAlg_of_positive M.P M.positive
      ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ) hnodes).1 hci
  have hpoint := hAlg (tuple4XYZ a b c d)
  have hpoint' :
      marginalMass M.P (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ))
          hnodes (tuple4XYZ a b c d) *
        marginalMass M.P ({1, 3} : Finset ℕ) (subset_Z_of_union hnodes) (tuple4Z b d) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ))
          (subset_XZ_of_union hnodes) (tuple4XZ a b d) *
        marginalMass M.P (({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ))
          (subset_YZ_of_union hnodes) (tuple4YZ b c d) := by
    have hZr := tuple4XYZ_restrict_Z (a := a) (b := b) (c := c) (d := d)
    have hXZr := tuple4XYZ_restrict_XZ (a := a) (b := b) (c := c) (d := d)
    have hYZr := tuple4XYZ_restrict_YZ (a := a) (b := b) (c := c) (d := d)
    rw [hZr, hXZr, hYZr] at hpoint
    exact hpoint
  calc
    (project4PMF M h0 h1 h2 h3).pmf (a, b, c, d) *
        marginalYWMass (project4PMF M h0 h1 h2 h3) (b, d) =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ))
          hnodes (tuple4XYZ a b c d) *
        marginalMass M.P ({1, 3} : Finset ℕ) (subset_Z_of_union hnodes) (tuple4Z b d) := by
        rw [project4_pmf_eq_marginalXYZ M h0 h1 h2 h3 hnodes a b c d,
          project4_context_bd_eq_marginalZ M h0 h1 h2 h3 (subset_Z_of_union hnodes) b d]
    _ =
      marginalMass M.P (({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ))
          (subset_XZ_of_union hnodes) (tuple4XZ a b d) *
        marginalMass M.P (({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ))
          (subset_YZ_of_union hnodes) (tuple4YZ b c d) := hpoint'
    _ =
      marginalXYWMass (project4PMF M h0 h1 h2 h3) (a, b, d) *
        marginalYZWMass (project4PMF M h0 h1 h2 h3) (b, c, d) := by
        rw [project4_sum_c_eq_marginalXZ M h0 h1 h2 h3 (subset_XZ_of_union hnodes) a b d,
          project4_sum_a_eq_marginalYZ M h0 h1 h2 h3 (subset_YZ_of_union hnodes) b c d]


end AssignmentSemantics

end

end CausalQIF.UnsafeBridge
