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

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem reindex_inv
    {S T : Finset ℕ} (hST : ∀ n, n ∈ S ↔ n ∈ T)
    (a : AssignOn Var S) :
    Reindex (fun n => (hST n).symm) (Reindex hST a) = a := by
  ext t
  cases t with
  | mk n hn =>
      simp [Reindex]

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem reindex_restrict
    {S T U : Finset ℕ}
    (hST : ∀ n, n ∈ S ↔ n ∈ T)
    (hSU : U ⊆ S) (hTU : U ⊆ T)
    (a : AssignOn Var S) (u : {n // n ∈ U}) :
    restrictAssign hTU (Reindex hST a) u = restrictAssign hSU a u := by
  simp [Reindex, restrictAssign]

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
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

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
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
            exact h2.symm
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
      _ = Reindex hST s := h1

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

private lemma subset_Z_of_XZ (X Z : Finset ℕ) :
    Z ⊆ X ∪ Z := by
  intro v hv
  simp only [mem_union]
  tauto

private lemma subset_Z_of_YZ (Y Z : Finset ℕ) :
    Z ⊆ Y ∪ Z := by
  intro v hv
  simp only [mem_union]
  tauto

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem restrictAssign_comp
    {S T U : Finset ℕ} (hST : S ⊆ T) (hTU : T ⊆ U)
    (hSU : S ⊆ U) (a : AssignOn Var U) :
    restrictAssign hST (restrictAssign hTU a) = restrictAssign hSU a := by
  ext i
  rfl

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem restrictAssignment_comp
    {S T : Finset ℕ} (hST : S ⊆ T)
    (hT : T ⊆ G.nodes) (hS : S ⊆ G.nodes)
    (a : Assignment G Var) :
    restrictAssign hST (restrictAssignment hT a) =
      restrictAssignment hS a := by
  ext i
  rfl

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

private theorem marginalMass_eq_sum_restrict
    {S T : Finset ℕ} (hST : S ⊆ T)
    (hS : S ⊆ G.nodes) (hT : T ⊆ G.nodes)
    (P : FinitePMF (Assignment G Var)) (s : AssignOn Var S) :
    marginalMass P S hS s =
      ∑ t : AssignOn Var T,
        if restrictAssign hST t = s then marginalMass P T hT t else 0 := by
  classical
  unfold marginalMass
  calc
    (∑ a : Assignment G Var,
        if restrictAssignment hS a = s then P.pmf a else 0)
        =
      ∑ a : Assignment G Var, ∑ t : AssignOn Var T,
        if restrictAssignment hT a = t then
          if restrictAssign hST t = s then P.pmf a else 0
        else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hcomp :
          restrictAssign hST (restrictAssignment hT a) =
            restrictAssignment hS a :=
        restrictAssignment_comp (G := G) (Var := Var) hST hT hS a
      rw [Fintype.sum_ite_eq (i := restrictAssignment hT a)]
      rw [hcomp]
    _ =
      ∑ t : AssignOn Var T, ∑ a : Assignment G Var,
        if restrictAssignment hT a = t then
          if restrictAssign hST t = s then P.pmf a else 0
        else 0 := by
      exact Finset.sum_comm
    _ =
      ∑ t : AssignOn Var T,
        if restrictAssign hST t = s then
          ∑ a : Assignment G Var,
            if restrictAssignment hT a = t then P.pmf a else 0
        else 0 := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      by_cases hts : restrictAssign hST t = s
      · simp [hts]
      · simp [hts]
    _ =
      ∑ t : AssignOn Var T,
        if restrictAssign hST t = s then
          marginalMass P T hT t
        else 0 := by
      rfl

/-- Unnormalized conditional sum over the context event `Z = z`. -/
def contextRestrictedSum (P : FinitePMF (Assignment G Var)) (Z : Finset ℕ)
    (hZ : Z ⊆ G.nodes) (z : AssignOn Var Z)
    (φ : Assignment G Var → ℝ) : ℝ :=
  ∑ a : Assignment G Var,
    if restrictAssignment hZ a = z then P.pmf a * φ a else 0

private def indicator {α : Type} [DecidableEq α] (x : α) (y : α) : ℝ :=
  if y = x then 1 else 0

private theorem marginalMass_nonneg
    (P : FinitePMF (Assignment G Var)) (S : Finset ℕ)
    (hnodes : S ⊆ G.nodes) (s : AssignOn Var S) :
    0 ≤ marginalMass P S hnodes s := by
  classical
  unfold marginalMass
  exact Finset.sum_nonneg fun a _ => by
    by_cases h : restrictAssignment hnodes a = s
    · simp [h, P.pmf_nonneg a]
    · simp [h]

private theorem contextRestrictedSum_expand_by_indicator
    (P : FinitePMF (Assignment G Var)) (Z : Finset ℕ)
    (hZ : Z ⊆ G.nodes) (z : AssignOn Var Z)
    {A : Type} [Fintype A] [DecidableEq A]
    (r : Assignment G Var → A) (ψ : Assignment G Var → ℝ) (u : A → ℝ) :
    contextRestrictedSum P Z hZ z (fun a => ψ a * u (r a)) =
      ∑ x : A, u x *
        contextRestrictedSum P Z hZ z
          (fun a => ψ a * indicator x (r a)) := by
  classical
  unfold contextRestrictedSum indicator
  calc
    (∑ a : Assignment G Var,
      if restrictAssignment hZ a = z then P.pmf a * (ψ a * u (r a)) else 0)
        =
      ∑ a : Assignment G Var,
        if restrictAssignment hZ a = z then
          ∑ x : A, u x * (P.pmf a * (ψ a * (if r a = x then 1 else 0)))
        else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have hbasis : (∑ x : A, u x * (if r a = x then (1 : ℝ) else 0)) = u (r a) := by
        calc
          (∑ x : A, u x * (if r a = x then (1 : ℝ) else 0))
              = ∑ x : A, if r a = x then u x else 0 := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                by_cases hr : r a = x
                · simp [hr]
                · simp [hr]
          _ = u (r a) := Fintype.sum_ite_eq (i := r a) (f := u)
      by_cases hctx : restrictAssignment hZ a = z
      · rw [if_pos hctx]
        calc
          P.pmf a * (ψ a * u (r a))
              = P.pmf a * (ψ a * (∑ x : A, u x * (if r a = x then (1 : ℝ) else 0))) := by
                rw [hbasis]
          _ = P.pmf a *
              (∑ x : A, ψ a * (u x * (if r a = x then (1 : ℝ) else 0))) := by
            rw [Finset.mul_sum]
          _ = ∑ x : A, P.pmf a * (ψ a * (u x * (if r a = x then 1 else 0))) := by
            rw [Finset.mul_sum]
          _ = ∑ x : A, u x * (P.pmf a * (ψ a * (if r a = x then 1 else 0))) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
          _ =
              (if restrictAssignment hZ a = z then
                ∑ x : A, u x * (P.pmf a * (ψ a * (if r a = x then 1 else 0)))
              else 0) := by
            rw [if_pos hctx]
      · simp [hctx]
    _ =
      ∑ a : Assignment G Var, ∑ x : A,
        if restrictAssignment hZ a = z then
          u x * (P.pmf a * (ψ a * (if r a = x then 1 else 0)))
        else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hctx : restrictAssignment hZ a = z
      · simp [hctx]
      · simp [hctx]
    _ =
      ∑ x : A, ∑ a : Assignment G Var,
        if restrictAssignment hZ a = z then
          u x * (P.pmf a * (ψ a * (if r a = x then 1 else 0)))
        else 0 := by
      rw [Finset.sum_comm]
    _ =
      ∑ x : A, u x *
        (∑ a : Assignment G Var,
          if restrictAssignment hZ a = z then
            P.pmf a * (ψ a * (if r a = x then 1 else 0))
          else 0) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hctx : restrictAssignment hZ a = z
      · simp [hctx]
      · simp [hctx]
    _ =
      ∑ x : A, u x *
        (∑ a : Assignment G Var,
          if restrictAssignment hZ a = z then
            P.pmf a * (ψ a * (if r a = x then 1 else 0))
          else 0) := rfl

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem restrict_XZ_then_Z_eq_restrict_XYZ_then_Z
    (X Y Z : Finset ℕ) (xyz : AssignOn Var (X ∪ Y ∪ Z)) :
    restrictAssign (subset_Z_of_XZ X Z)
        (restrictAssign (subset_XZ_of_XYZ X Y Z) xyz) =
      restrictAssign (subset_Z_of_XYZ X Y Z) xyz := by
  exact restrictAssign_comp
    (hST := subset_Z_of_XZ X Z)
    (hTU := subset_XZ_of_XYZ X Y Z)
    (hSU := subset_Z_of_XYZ X Y Z)
    xyz

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem restrict_YZ_then_Z_eq_restrict_XYZ_then_Z
    (X Y Z : Finset ℕ) (xyz : AssignOn Var (X ∪ Y ∪ Z)) :
    restrictAssign (subset_Z_of_YZ Y Z)
        (restrictAssign (subset_YZ_of_XYZ X Y Z) xyz) =
      restrictAssign (subset_Z_of_XYZ X Y Z) xyz := by
  exact restrictAssign_comp
    (hST := subset_Z_of_YZ Y Z)
    (hTU := subset_YZ_of_XYZ X Y Z)
    (hSU := subset_Z_of_XYZ X Y Z)
    xyz

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
      simp [FinitePMF.sum_one] at hsum
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

private theorem marginalMass_pos_of_strictlyPositive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (S : Finset ℕ) (hnodes : S ⊆ G.nodes) (s : AssignOn Var S) :
    0 < marginalMass P S hnodes s := by
  simpa [contextMass] using
    contextMass_pos_of_strictlyPositive (G := G) (Var := Var) P hpos S hnodes s

private theorem contextRestrictedSum_indicator_XZ_eq_marginalMass
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (z : AssignOn Var Z) (xz : AssignOn Var (X ∪ Z))
    (hzx : restrictAssign (subset_Z_of_XZ X Z) xz = z) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes) z
        (fun a => indicator xz
          (restrictAssignment (subset_XZ_of_union hnodes) a)) =
      marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes) xz := by
  classical
  unfold contextRestrictedSum marginalMass indicator
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases hx : restrictAssignment (subset_XZ_of_union hnodes) a = xz
  · have hz : restrictAssignment (subset_Z_of_union hnodes) a = z := by
      calc
        restrictAssignment (subset_Z_of_union hnodes) a =
            restrictAssign (subset_Z_of_XZ X Z)
              (restrictAssignment (subset_XZ_of_union hnodes) a) := by
              exact (restrictAssignment_comp
                (G := G) (Var := Var)
                (hST := subset_Z_of_XZ X Z)
                (hT := subset_XZ_of_union hnodes)
                (hS := subset_Z_of_union hnodes) a).symm
        _ = restrictAssign (subset_Z_of_XZ X Z) xz := by rw [hx]
        _ = z := hzx
    simp [hx, hz]
  · simp [hx]

private theorem contextRestrictedSum_indicator_YZ_eq_marginalMass
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (z : AssignOn Var Z) (yz : AssignOn Var (Y ∪ Z))
    (hzy : restrictAssign (subset_Z_of_YZ Y Z) yz = z) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes) z
        (fun a => indicator yz
          (restrictAssignment (subset_YZ_of_union hnodes) a)) =
      marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz := by
  classical
  unfold contextRestrictedSum marginalMass indicator
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases hy : restrictAssignment (subset_YZ_of_union hnodes) a = yz
  · have hz : restrictAssignment (subset_Z_of_union hnodes) a = z := by
      calc
        restrictAssignment (subset_Z_of_union hnodes) a =
            restrictAssign (subset_Z_of_YZ Y Z)
              (restrictAssignment (subset_YZ_of_union hnodes) a) := by
              exact (restrictAssignment_comp
                (G := G) (Var := Var)
                (hST := subset_Z_of_YZ Y Z)
                (hT := subset_YZ_of_union hnodes)
                (hS := subset_Z_of_union hnodes) a).symm
        _ = restrictAssign (subset_Z_of_YZ Y Z) yz := by rw [hy]
        _ = z := hzy
    simp [hy, hz]
  · simp [hy]

private theorem contextRestrictedSum_indicator_XZ_eq_if_marginalMass
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (z : AssignOn Var Z) (xz : AssignOn Var (X ∪ Z)) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes) z
        (fun a => indicator xz
          (restrictAssignment (subset_XZ_of_union hnodes) a)) =
      if restrictAssign (subset_Z_of_XZ X Z) xz = z then
        marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes) xz
      else 0 := by
  classical
  by_cases hzx : restrictAssign (subset_Z_of_XZ X Z) xz = z
  · simp [hzx, contextRestrictedSum_indicator_XZ_eq_marginalMass
      (G := G) (Var := Var) P X Y Z hnodes z xz hzx]
  · have hzero :
        contextRestrictedSum P Z (subset_Z_of_union hnodes) z
          (fun a => indicator xz
            (restrictAssignment (subset_XZ_of_union hnodes) a)) = 0 := by
      unfold contextRestrictedSum indicator
      refine Finset.sum_eq_zero ?_
      intro a ha
      by_cases hctx : restrictAssignment (subset_Z_of_union hnodes) a = z
      · by_cases hx : restrictAssignment (subset_XZ_of_union hnodes) a = xz
        · have hzx' : restrictAssign (subset_Z_of_XZ X Z) xz = z := by
            calc
              restrictAssign (subset_Z_of_XZ X Z) xz =
                  restrictAssign (subset_Z_of_XZ X Z)
                    (restrictAssignment (subset_XZ_of_union hnodes) a) := by rw [hx]
              _ = restrictAssignment (subset_Z_of_union hnodes) a := by
                exact restrictAssignment_comp
                  (G := G) (Var := Var)
                  (hST := subset_Z_of_XZ X Z)
                  (hT := subset_XZ_of_union hnodes)
                  (hS := subset_Z_of_union hnodes) a
              _ = z := hctx
          exact False.elim (hzx hzx')
        · simp [hctx, hx]
      · simp [hctx]
    simp [hzx, hzero]

private theorem contextRestrictedSum_indicator_YZ_eq_if_marginalMass
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (z : AssignOn Var Z) (yz : AssignOn Var (Y ∪ Z)) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes) z
        (fun a => indicator yz
          (restrictAssignment (subset_YZ_of_union hnodes) a)) =
      if restrictAssign (subset_Z_of_YZ Y Z) yz = z then
        marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz
      else 0 := by
  classical
  by_cases hzy : restrictAssign (subset_Z_of_YZ Y Z) yz = z
  · simp [hzy, contextRestrictedSum_indicator_YZ_eq_marginalMass
      (G := G) (Var := Var) P X Y Z hnodes z yz hzy]
  · have hzero :
        contextRestrictedSum P Z (subset_Z_of_union hnodes) z
          (fun a => indicator yz
            (restrictAssignment (subset_YZ_of_union hnodes) a)) = 0 := by
      unfold contextRestrictedSum indicator
      refine Finset.sum_eq_zero ?_
      intro a ha
      by_cases hctx : restrictAssignment (subset_Z_of_union hnodes) a = z
      · by_cases hy : restrictAssignment (subset_YZ_of_union hnodes) a = yz
        · have hzy' : restrictAssign (subset_Z_of_YZ Y Z) yz = z := by
            calc
              restrictAssign (subset_Z_of_YZ Y Z) yz =
                  restrictAssign (subset_Z_of_YZ Y Z)
                    (restrictAssignment (subset_YZ_of_union hnodes) a) := by rw [hy]
              _ = restrictAssignment (subset_Z_of_union hnodes) a := by
                exact restrictAssignment_comp
                  (G := G) (Var := Var)
                  (hST := subset_Z_of_YZ Y Z)
                  (hT := subset_YZ_of_union hnodes)
                  (hS := subset_Z_of_union hnodes) a
              _ = z := hctx
          exact False.elim (hzy hzy')
        · simp [hctx, hy]
      · simp [hctx]
    simp [hzy, hzero]

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem restrictAssignment_XYZ_eq_iff_XZ_YZ
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (a : Assignment G Var) (xyz : AssignOn Var (X ∪ Y ∪ Z)) :
    restrictAssignment hnodes a = xyz ↔
      restrictAssignment (subset_XZ_of_union hnodes) a =
          restrictAssign (subset_XZ_of_XYZ X Y Z) xyz ∧
        restrictAssignment (subset_YZ_of_union hnodes) a =
          restrictAssign (subset_YZ_of_XYZ X Y Z) xyz := by
  constructor
  · intro h
    constructor
    · calc
        restrictAssignment (subset_XZ_of_union hnodes) a =
            restrictAssign (subset_XZ_of_XYZ X Y Z)
              (restrictAssignment hnodes a) := by
              exact (restrictAssignment_comp
                (G := G) (Var := Var)
                (hST := subset_XZ_of_XYZ X Y Z)
                (hT := hnodes)
                (hS := subset_XZ_of_union hnodes) a).symm
        _ = restrictAssign (subset_XZ_of_XYZ X Y Z) xyz := by rw [h]
    · calc
        restrictAssignment (subset_YZ_of_union hnodes) a =
            restrictAssign (subset_YZ_of_XYZ X Y Z)
              (restrictAssignment hnodes a) := by
              exact (restrictAssignment_comp
                (G := G) (Var := Var)
                (hST := subset_YZ_of_XYZ X Y Z)
                (hT := hnodes)
                (hS := subset_YZ_of_union hnodes) a).symm
        _ = restrictAssign (subset_YZ_of_XYZ X Y Z) xyz := by rw [h]
  · rintro ⟨hXZ, hYZ⟩
    ext i
    rcases i with ⟨n, hn⟩
    by_cases hnX : n ∈ X
    · have hval := congrFun hXZ ⟨n, by simp [hnX]⟩
      simpa [restrictAssignment, restrictAssign] using hval
    · by_cases hnY : n ∈ Y
      · have hval := congrFun hYZ ⟨n, by simp [hnY]⟩
        simpa [restrictAssignment, restrictAssign] using hval
      · have hnZ : n ∈ Z := by
          simp only [mem_union] at hn
          tauto
        have hval := congrFun hXZ ⟨n, by simp [hnZ]⟩
        simpa [restrictAssignment, restrictAssign] using hval

omit [∀ n, Fintype (Var n)] [∀ n, DecidableEq (Var n)] in
private theorem assign_XYZ_ext_of_XZ_YZ
    (X Y Z : Finset ℕ)
    {u v : AssignOn Var (X ∪ Y ∪ Z)}
    (hXZ :
      restrictAssign (subset_XZ_of_XYZ X Y Z) u =
        restrictAssign (subset_XZ_of_XYZ X Y Z) v)
    (hYZ :
      restrictAssign (subset_YZ_of_XYZ X Y Z) u =
        restrictAssign (subset_YZ_of_XYZ X Y Z) v) :
    u = v := by
  ext i
  rcases i with ⟨n, hn⟩
  by_cases hnX : n ∈ X
  · have hval := congrFun hXZ ⟨n, by simp [hnX]⟩
    simpa [restrictAssign] using hval
  · by_cases hnY : n ∈ Y
    · have hval := congrFun hYZ ⟨n, by simp [hnY]⟩
      simpa [restrictAssign] using hval
    · have hnZ : n ∈ Z := by
        simp only [mem_union] at hn
        tauto
      have hval := congrFun hXZ ⟨n, by simp [hnZ]⟩
      simpa [restrictAssign] using hval

private def compatibleXZ_YZ
    (X Y Z : Finset ℕ)
    (xz : AssignOn Var (X ∪ Z)) (yz : AssignOn Var (Y ∪ Z)) : Prop :=
  ∃ xyz : AssignOn Var (X ∪ Y ∪ Z),
    restrictAssign (subset_XZ_of_XYZ X Y Z) xyz = xz ∧
      restrictAssign (subset_YZ_of_XYZ X Y Z) xyz = yz

private def compatibleYZFinset
    (X Y Z : Finset ℕ) (xz : AssignOn Var (X ∪ Z)) :
    Finset (AssignOn Var (Y ∪ Z)) :=
  (Finset.univ.filter
    (fun xyz : AssignOn Var (X ∪ Y ∪ Z) =>
      restrictAssign (subset_XZ_of_XYZ X Y Z) xyz = xz)).image
    (fun xyz => restrictAssign (subset_YZ_of_XYZ X Y Z) xyz)

private theorem mem_compatibleYZFinset_iff
    (X Y Z : Finset ℕ)
    (xz : AssignOn Var (X ∪ Z)) (yz : AssignOn Var (Y ∪ Z)) :
    yz ∈ compatibleYZFinset X Y Z xz ↔ compatibleXZ_YZ X Y Z xz yz := by
  classical
  constructor
  · intro hyz
    rcases Finset.mem_image.1 hyz with ⟨xyz, hxyzMem, hyzEq⟩
    have hxzEq :
        restrictAssign (subset_XZ_of_XYZ X Y Z) xyz = xz := by
      simpa [compatibleYZFinset] using (Finset.mem_filter.1 hxyzMem).2
    exact ⟨xyz, hxzEq, by simpa using hyzEq⟩
  · rintro ⟨xyz, hxzEq, hyzEq⟩
    apply Finset.mem_image.2
    refine ⟨xyz, ?_, hyzEq⟩
    simp [hxzEq]

private theorem compatibleYZFinset_subset_zSet
    (X Y Z : Finset ℕ)
    (z : AssignOn Var Z) (xz : AssignOn Var (X ∪ Z))
    (hzx : restrictAssign (subset_Z_of_XZ X Z) xz = z) :
    compatibleYZFinset X Y Z xz ⊆
      Finset.univ.filter
        (fun yz : AssignOn Var (Y ∪ Z) =>
          restrictAssign (subset_Z_of_YZ Y Z) yz = z) := by
  classical
  intro yz hyz
  rcases (mem_compatibleYZFinset_iff (Var := Var) X Y Z xz yz).1 hyz with
    ⟨xyz, hxzEq, hyzEq⟩
  have hzyz : restrictAssign (subset_Z_of_YZ Y Z) yz = z := by
    calc
      restrictAssign (subset_Z_of_YZ Y Z) yz =
          restrictAssign (subset_Z_of_YZ Y Z)
            (restrictAssign (subset_YZ_of_XYZ X Y Z) xyz) := by rw [hyzEq]
      _ = restrictAssign (subset_Z_of_XYZ X Y Z) xyz := by
        exact restrict_YZ_then_Z_eq_restrict_XYZ_then_Z
          (Var := Var) X Y Z xyz
      _ = restrictAssign (subset_Z_of_XZ X Z)
            (restrictAssign (subset_XZ_of_XYZ X Y Z) xyz) := by
        exact (restrict_XZ_then_Z_eq_restrict_XYZ_then_Z
          (Var := Var) X Y Z xyz).symm
      _ = restrictAssign (subset_Z_of_XZ X Z) xz := by rw [hxzEq]
      _ = z := hzx
  simp [hzyz]

private theorem contextRestrictedSum_indicator_XZ_YZ_eq_zero_of_incompatible
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (z : AssignOn Var Z)
    (xz : AssignOn Var (X ∪ Z)) (yz : AssignOn Var (Y ∪ Z))
    (hnot : ¬ compatibleXZ_YZ X Y Z xz yz) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes) z
        (fun a =>
          indicator xz (restrictAssignment (subset_XZ_of_union hnodes) a) *
          indicator yz (restrictAssignment (subset_YZ_of_union hnodes) a)) = 0 := by
  classical
  unfold contextRestrictedSum indicator
  refine Finset.sum_eq_zero ?_
  intro a ha
  by_cases hctx : restrictAssignment (subset_Z_of_union hnodes) a = z
  · by_cases hx : restrictAssignment (subset_XZ_of_union hnodes) a = xz
    · by_cases hy : restrictAssignment (subset_YZ_of_union hnodes) a = yz
      · have hcompat : compatibleXZ_YZ X Y Z xz yz := by
          refine ⟨restrictAssignment hnodes a, ?_, ?_⟩
          · calc
              restrictAssign (subset_XZ_of_XYZ X Y Z)
                  (restrictAssignment hnodes a) =
                restrictAssignment (subset_XZ_of_union hnodes) a := by
                  exact restrictAssignment_comp
                    (G := G) (Var := Var)
                    (hST := subset_XZ_of_XYZ X Y Z)
                    (hT := hnodes)
                    (hS := subset_XZ_of_union hnodes) a
              _ = xz := hx
          · calc
              restrictAssign (subset_YZ_of_XYZ X Y Z)
                  (restrictAssignment hnodes a) =
                restrictAssignment (subset_YZ_of_union hnodes) a := by
                  exact restrictAssignment_comp
                    (G := G) (Var := Var)
                    (hST := subset_YZ_of_XYZ X Y Z)
                    (hT := hnodes)
                    (hS := subset_YZ_of_union hnodes) a
              _ = yz := hy
        exact False.elim (hnot hcompat)
      · simp [hctx, hx, hy]
    · simp [hctx, hx]
  · simp [hctx]

private theorem contextRestrictedSum_indicator_XZ_YZ_eq_zero_of_XZ_context_ne
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (z : AssignOn Var Z)
    (xz : AssignOn Var (X ∪ Z)) (yz : AssignOn Var (Y ∪ Z))
    (hzx : restrictAssign (subset_Z_of_XZ X Z) xz ≠ z) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes) z
        (fun a =>
          indicator xz (restrictAssignment (subset_XZ_of_union hnodes) a) *
          indicator yz (restrictAssignment (subset_YZ_of_union hnodes) a)) = 0 := by
  classical
  unfold contextRestrictedSum indicator
  refine Finset.sum_eq_zero ?_
  intro a ha
  by_cases hctx : restrictAssignment (subset_Z_of_union hnodes) a = z
  · by_cases hx : restrictAssignment (subset_XZ_of_union hnodes) a = xz
    · have hzx' : restrictAssign (subset_Z_of_XZ X Z) xz = z := by
        calc
          restrictAssign (subset_Z_of_XZ X Z) xz =
              restrictAssign (subset_Z_of_XZ X Z)
                (restrictAssignment (subset_XZ_of_union hnodes) a) := by rw [hx]
          _ = restrictAssignment (subset_Z_of_union hnodes) a := by
            exact restrictAssignment_comp
              (G := G) (Var := Var)
              (hST := subset_Z_of_XZ X Z)
              (hT := subset_XZ_of_union hnodes)
              (hS := subset_Z_of_union hnodes) a
          _ = z := hctx
      exact False.elim (hzx hzx')
    · simp [hctx, hx]
  · simp [hctx]

private theorem contextRestrictedSum_indicator_XZ_YZ_eq_zero_of_YZ_context_ne
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (z : AssignOn Var Z)
    (xz : AssignOn Var (X ∪ Z)) (yz : AssignOn Var (Y ∪ Z))
    (hzy : restrictAssign (subset_Z_of_YZ Y Z) yz ≠ z) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes) z
        (fun a =>
          indicator xz (restrictAssignment (subset_XZ_of_union hnodes) a) *
          indicator yz (restrictAssignment (subset_YZ_of_union hnodes) a)) = 0 := by
  classical
  unfold contextRestrictedSum indicator
  refine Finset.sum_eq_zero ?_
  intro a ha
  by_cases hctx : restrictAssignment (subset_Z_of_union hnodes) a = z
  · by_cases hy : restrictAssignment (subset_YZ_of_union hnodes) a = yz
    · have hzy' : restrictAssign (subset_Z_of_YZ Y Z) yz = z := by
        calc
          restrictAssign (subset_Z_of_YZ Y Z) yz =
              restrictAssign (subset_Z_of_YZ Y Z)
                (restrictAssignment (subset_YZ_of_union hnodes) a) := by rw [hy]
          _ = restrictAssignment (subset_Z_of_union hnodes) a := by
            exact restrictAssignment_comp
              (G := G) (Var := Var)
              (hST := subset_Z_of_YZ Y Z)
              (hT := subset_YZ_of_union hnodes)
              (hS := subset_Z_of_union hnodes) a
          _ = z := hctx
      exact False.elim (hzy hzy')
    · simp [hctx, hy]
  · simp [hctx]

set_option maxHeartbeats 800000 in
private theorem compatible_YZ_sum_eq_context_of_CIAlg
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hAlg : CIAlg P X Y Z hnodes)
    (z : AssignOn Var Z) (xz : AssignOn Var (X ∪ Z))
    (hzx : restrictAssign (subset_Z_of_XZ X Z) xz = z) :
    ∑ yz ∈ compatibleYZFinset X Y Z xz,
        marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz =
      contextMass P Z (subset_Z_of_union hnodes) z := by
  classical
  let xzOf : AssignOn Var (X ∪ Y ∪ Z) → AssignOn Var (X ∪ Z) :=
    fun xyz => restrictAssign (subset_XZ_of_XYZ X Y Z) xyz
  let yzOf : AssignOn Var (X ∪ Y ∪ Z) → AssignOn Var (Y ∪ Z) :=
    fun xyz => restrictAssign (subset_YZ_of_XYZ X Y Z) xyz
  let zOf : AssignOn Var (X ∪ Y ∪ Z) → AssignOn Var Z :=
    fun xyz => restrictAssign (subset_Z_of_XYZ X Y Z) xyz
  let fiber : Finset (AssignOn Var (X ∪ Y ∪ Z)) :=
    Finset.univ.filter (fun xyz => xzOf xyz = xz)
  let image : Finset (AssignOn Var (Y ∪ Z)) := fiber.image yzOf
  let mXYZ : AssignOn Var (X ∪ Y ∪ Z) → ℝ :=
    fun xyz => marginalMass P (X ∪ Y ∪ Z) hnodes xyz
  let mXZ : ℝ := marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes) xz
  let mYZ : AssignOn Var (Y ∪ Z) → ℝ :=
    fun yz => marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz
  let mZ : ℝ := contextMass P Z (subset_Z_of_union hnodes) z
  have hmXZ_pos : 0 < mXZ := by
    simpa [mXZ] using
      (marginalMass_pos_of_strictlyPositive
        (G := G) (Var := Var) P hpos (X ∪ Z)
        (subset_XZ_of_union hnodes) xz)
  have hmXZ_ne : mXZ ≠ 0 := ne_of_gt hmXZ_pos
  have hpartXZ :
      mXZ = ∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
        if xzOf xyz = xz then mXYZ xyz else 0 := by
    simpa [mXZ, mXYZ, xzOf] using
      (marginalMass_eq_sum_restrict
        (G := G) (Var := Var)
        (hST := subset_XZ_of_XYZ X Y Z)
        (hS := subset_XZ_of_union hnodes)
        (hT := hnodes) P xz)
  have hsumAlg :
      (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
        if xzOf xyz = xz then mXYZ xyz * mZ else 0) =
      (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
        if xzOf xyz = xz then mXZ * mYZ (yzOf xyz) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro xyz hxyzMem
    by_cases hx : xzOf xyz = xz
    · have hzxyz : zOf xyz = z := by
        calc
          zOf xyz =
              restrictAssign (subset_Z_of_XZ X Z) (xzOf xyz) := by
                simpa [xzOf, zOf] using
                  (restrict_XZ_then_Z_eq_restrict_XYZ_then_Z
                    (Var := Var) X Y Z xyz).symm
          _ = restrictAssign (subset_Z_of_XZ X Z) xz := by rw [hx]
          _ = z := hzx
      have hci := hAlg xyz
      simpa [mXYZ, mXZ, mYZ, mZ, contextMass, xzOf, yzOf, zOf, hx, hzxyz] using hci
    · simp [hx]
  have hleft :
      (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
        if xzOf xyz = xz then mXYZ xyz * mZ else 0) = mXZ * mZ := by
    calc
      (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
        if xzOf xyz = xz then mXYZ xyz * mZ else 0)
          =
        (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
          if xzOf xyz = xz then mXYZ xyz else 0) * mZ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro xyz hxyzMem
        by_cases hx : xzOf xyz = xz
        · simp [hx]
        · simp [hx]
      _ = mXZ * mZ := by rw [← hpartXZ]
  have hright :
      (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
        if xzOf xyz = xz then mXZ * mYZ (yzOf xyz) else 0) =
        mXZ * (∑ xyz ∈ fiber, mYZ (yzOf xyz)) := by
    calc
      (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
        if xzOf xyz = xz then mXZ * mYZ (yzOf xyz) else 0)
          =
        mXZ * (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
          if xzOf xyz = xz then mYZ (yzOf xyz) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro xyz hxyzMem
        by_cases hx : xzOf xyz = xz
        · simp [hx]
        · simp [hx]
      _ = mXZ * (∑ xyz ∈ fiber, mYZ (yzOf xyz)) := by
        congr 1
        simpa [fiber] using
          (Finset.sum_filter
            (s := (Finset.univ : Finset (AssignOn Var (X ∪ Y ∪ Z))))
            (p := fun xyz => xzOf xyz = xz)
            (f := fun xyz => mYZ (yzOf xyz))).symm
  have hsumFiber :
      mZ = ∑ xyz ∈ fiber, mYZ (yzOf xyz) := by
    have hmul : mXZ * mZ = mXZ * (∑ xyz ∈ fiber, mYZ (yzOf xyz)) := by
      calc
        mXZ * mZ = (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
          if xzOf xyz = xz then mXYZ xyz * mZ else 0) := hleft.symm
        _ = (∑ xyz : AssignOn Var (X ∪ Y ∪ Z),
          if xzOf xyz = xz then mXZ * mYZ (yzOf xyz) else 0) := hsumAlg
        _ = mXZ * (∑ xyz ∈ fiber, mYZ (yzOf xyz)) := hright
    exact mul_left_cancel₀ hmXZ_ne hmul
  have hinj : Set.InjOn yzOf (↑fiber : Set (AssignOn Var (X ∪ Y ∪ Z))) := by
    intro u hu v hv huv
    have hu_xz : xzOf u = xz := by
      simpa [fiber] using hu
    have hv_xz : xzOf v = xz := by
      simpa [fiber] using hv
    apply assign_XYZ_ext_of_XZ_YZ (Var := Var) X Y Z
    · simp [xzOf, hu_xz, hv_xz]
    · simpa [yzOf] using huv
  have hsumImage :
      (∑ yz ∈ image, mYZ yz) = ∑ xyz ∈ fiber, mYZ (yzOf xyz) := by
    simpa [image] using
      (Finset.sum_image (s := fiber) (g := yzOf) (f := mYZ) hinj)
  calc
    (∑ yz ∈ compatibleYZFinset X Y Z xz,
        marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz)
        = ∑ yz ∈ image, mYZ yz := by
          rfl
    _ = ∑ xyz ∈ fiber, mYZ (yzOf xyz) := hsumImage
    _ = contextMass P Z (subset_Z_of_union hnodes) z := by
      simpa [mZ] using hsumFiber.symm

private theorem marginalMass_YZ_eq_zero_of_incompatible_CIAlg
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hAlg : CIAlg P X Y Z hnodes)
    (z : AssignOn Var Z) (xz : AssignOn Var (X ∪ Z))
    (yz : AssignOn Var (Y ∪ Z))
    (hzx : restrictAssign (subset_Z_of_XZ X Z) xz = z)
    (hzy : restrictAssign (subset_Z_of_YZ Y Z) yz = z)
    (hnot : ¬ compatibleXZ_YZ X Y Z xz yz) :
    marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz = 0 := by
  classical
  let compat : Finset (AssignOn Var (Y ∪ Z)) := compatibleYZFinset X Y Z xz
  let zSet : Finset (AssignOn Var (Y ∪ Z)) :=
    Finset.univ.filter
      (fun yz' : AssignOn Var (Y ∪ Z) =>
        restrictAssign (subset_Z_of_YZ Y Z) yz' = z)
  let mYZ : AssignOn Var (Y ∪ Z) → ℝ :=
    fun yz' => marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz'
  have hcompat_sum :
      ∑ yz' ∈ compat, mYZ yz' =
        contextMass P Z (subset_Z_of_union hnodes) z := by
    simpa [compat, mYZ] using
      (compatible_YZ_sum_eq_context_of_CIAlg
        (G := G) (Var := Var) P hpos X Y Z hnodes hAlg z xz hzx)
  have htotal :
      ∑ yz' ∈ zSet, mYZ yz' =
        contextMass P Z (subset_Z_of_union hnodes) z := by
    have hpart := marginalMass_eq_sum_restrict
      (G := G) (Var := Var)
      (hST := subset_Z_of_YZ Y Z)
      (hS := subset_Z_of_union hnodes)
      (hT := subset_YZ_of_union hnodes) P z
    calc
      ∑ yz' ∈ zSet, mYZ yz'
          =
        ∑ yz' : AssignOn Var (Y ∪ Z),
          if restrictAssign (subset_Z_of_YZ Y Z) yz' = z then mYZ yz' else 0 := by
        simpa [zSet] using
          (Finset.sum_filter
            (s := (Finset.univ : Finset (AssignOn Var (Y ∪ Z))))
            (p := fun yz' : AssignOn Var (Y ∪ Z) =>
              restrictAssign (subset_Z_of_YZ Y Z) yz' = z)
            (f := mYZ))
      _ = marginalMass P Z (subset_Z_of_union hnodes) z := by
        simpa [mYZ] using hpart.symm
      _ = contextMass P Z (subset_Z_of_union hnodes) z := by
        rfl
  have hsubset : compat ⊆ zSet := by
    simpa [compat, zSet] using
      (compatibleYZFinset_subset_zSet (Var := Var) X Y Z z xz hzx)
  have hyz_zSet : yz ∈ zSet := by
    simp [zSet, hzy]
  have hyz_not_compat : yz ∉ compat := by
    intro hyzCompat
    exact hnot ((mem_compatibleYZFinset_iff (Var := Var) X Y Z xz yz).1 (by
      simpa [compat] using hyzCompat))
  have hyz_sdiff : yz ∈ zSet \ compat := by
    simp [hyz_zSet, hyz_not_compat]
  have hdiff_sum :
      ∑ yz' ∈ zSet \ compat, mYZ yz' = 0 := by
    have hsdiff := Finset.sum_sdiff (s₁ := compat) (s₂ := zSet)
      (f := mYZ) hsubset
    have htmp :
        (∑ yz' ∈ zSet \ compat, mYZ yz') +
          contextMass P Z (subset_Z_of_union hnodes) z =
        contextMass P Z (subset_Z_of_union hnodes) z := by
      simpa [hcompat_sum, htotal] using hsdiff
    linarith
  have hyz_le :
      mYZ yz ≤ ∑ yz' ∈ zSet \ compat, mYZ yz' := by
    exact Finset.single_le_sum
      (s := zSet \ compat)
      (f := mYZ)
      (by
        intro yz' hyz'
        exact marginalMass_nonneg P (Y ∪ Z) (subset_YZ_of_union hnodes) yz')
      hyz_sdiff
  have hyz_nonneg : 0 ≤ mYZ yz :=
    marginalMass_nonneg P (Y ∪ Z) (subset_YZ_of_union hnodes) yz
  have hyz_le_zero : mYZ yz ≤ 0 := by
    simpa [hdiff_sum] using hyz_le
  exact le_antisymm hyz_le_zero hyz_nonneg

private theorem contextRestrictedSum_indicator_XZ_YZ_eq_marginalMass_of_xyz
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (xyz : AssignOn Var (X ∪ Y ∪ Z)) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes)
        (restrictAssign (subset_Z_of_XYZ X Y Z) xyz)
        (fun a =>
          indicator (restrictAssign (subset_XZ_of_XYZ X Y Z) xyz)
            (restrictAssignment (subset_XZ_of_union hnodes) a) *
          indicator (restrictAssign (subset_YZ_of_XYZ X Y Z) xyz)
            (restrictAssignment (subset_YZ_of_union hnodes) a)) =
      marginalMass P (X ∪ Y ∪ Z) hnodes xyz := by
  classical
  unfold contextRestrictedSum marginalMass indicator
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases hfull : restrictAssignment hnodes a = xyz
  · have hXZ :
        restrictAssignment (subset_XZ_of_union hnodes) a =
          restrictAssign (subset_XZ_of_XYZ X Y Z) xyz :=
      ((restrictAssignment_XYZ_eq_iff_XZ_YZ
        (G := G) (Var := Var) X Y Z hnodes a xyz).1 hfull).1
    have hYZ :
        restrictAssignment (subset_YZ_of_union hnodes) a =
          restrictAssign (subset_YZ_of_XYZ X Y Z) xyz :=
      ((restrictAssignment_XYZ_eq_iff_XZ_YZ
        (G := G) (Var := Var) X Y Z hnodes a xyz).1 hfull).2
    have hZ : restrictAssignment (subset_Z_of_union hnodes) a =
        restrictAssign (subset_Z_of_XYZ X Y Z) xyz := by
      calc
        restrictAssignment (subset_Z_of_union hnodes) a =
            restrictAssign (subset_Z_of_XYZ X Y Z)
              (restrictAssignment hnodes a) := by
              exact (restrictAssignment_comp
                (G := G) (Var := Var)
                (hST := subset_Z_of_XYZ X Y Z)
                (hT := hnodes)
                (hS := subset_Z_of_union hnodes) a).symm
        _ = restrictAssign (subset_Z_of_XYZ X Y Z) xyz := by rw [hfull]
    simp [hfull, hXZ, hYZ, hZ]
  · by_cases hZ : restrictAssignment (subset_Z_of_union hnodes) a =
        restrictAssign (subset_Z_of_XYZ X Y Z) xyz
    · by_cases hXZ :
        restrictAssignment (subset_XZ_of_union hnodes) a =
          restrictAssign (subset_XZ_of_XYZ X Y Z) xyz
      · by_cases hYZ :
          restrictAssignment (subset_YZ_of_union hnodes) a =
            restrictAssign (subset_YZ_of_XYZ X Y Z) xyz
        · have hfull' : restrictAssignment hnodes a = xyz :=
            (restrictAssignment_XYZ_eq_iff_XZ_YZ
              (G := G) (Var := Var) X Y Z hnodes a xyz).2 ⟨hXZ, hYZ⟩
          exact False.elim (hfull hfull')
        · simp [hfull, hZ, hXZ, hYZ]
      · simp [hfull, hZ, hXZ]
    · simp [hfull, hZ]

private theorem conditionalExpectation_indicator_factor_of_CIAlg
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (hAlg : CIAlg P X Y Z hnodes)
    (z : AssignOn Var Z)
    (xz : AssignOn Var (X ∪ Z)) (yz : AssignOn Var (Y ∪ Z)) :
    conditionalExpectation P Z (subset_Z_of_union hnodes) z
        (fun a =>
          indicator xz (restrictAssign (subset_XZ_of_union hnodes) a) *
          indicator yz (restrictAssign (subset_YZ_of_union hnodes) a)) =
      conditionalExpectation P Z (subset_Z_of_union hnodes) z
        (fun a => indicator xz (restrictAssign (subset_XZ_of_union hnodes) a)) *
      conditionalExpectation P Z (subset_Z_of_union hnodes) z
        (fun a => indicator yz (restrictAssign (subset_YZ_of_union hnodes) a)) := by
  classical
  let mZ : ℝ := contextMass P Z (subset_Z_of_union hnodes) z
  have hmZ_pos : 0 < mZ := by
    simpa [mZ] using
      (contextMass_pos_of_strictlyPositive
        (G := G) (Var := Var) P hpos Z (subset_Z_of_union hnodes) z)
  have hmZ_ne : mZ ≠ 0 := ne_of_gt hmZ_pos
  by_cases hzx : restrictAssign (subset_Z_of_XZ X Z) xz = z
  · by_cases hzy : restrictAssign (subset_Z_of_YZ Y Z) yz = z
    · by_cases hcompat : compatibleXZ_YZ X Y Z xz yz
      · rcases hcompat with ⟨xyz, hxyz_xz, hxyz_yz⟩
        have hzxyz : restrictAssign (subset_Z_of_XYZ X Y Z) xyz = z := by
          calc
            restrictAssign (subset_Z_of_XYZ X Y Z) xyz =
                restrictAssign (subset_Z_of_XZ X Z)
                  (restrictAssign (subset_XZ_of_XYZ X Y Z) xyz) := by
                  exact (restrict_XZ_then_Z_eq_restrict_XYZ_then_Z
                    (Var := Var) X Y Z xyz).symm
            _ = restrictAssign (subset_Z_of_XZ X Z) xz := by rw [hxyz_xz]
            _ = z := hzx
        have hprod :
            contextRestrictedSum P Z (subset_Z_of_union hnodes) z
              (fun a =>
                indicator xz (restrictAssign (subset_XZ_of_union hnodes) a) *
                indicator yz (restrictAssign (subset_YZ_of_union hnodes) a)) =
              marginalMass P (X ∪ Y ∪ Z) hnodes xyz := by
          simpa [restrictAssignment, hxyz_xz, hxyz_yz, hzxyz] using
            (contextRestrictedSum_indicator_XZ_YZ_eq_marginalMass_of_xyz
              (G := G) (Var := Var) P X Y Z hnodes xyz)
        have hX :
            contextRestrictedSum P Z (subset_Z_of_union hnodes) z
              (fun a => indicator xz
                (restrictAssign (subset_XZ_of_union hnodes) a)) =
              marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes) xz := by
          simpa [restrictAssignment] using
            (contextRestrictedSum_indicator_XZ_eq_marginalMass
              (G := G) (Var := Var) P X Y Z hnodes z xz hzx)
        have hY :
            contextRestrictedSum P Z (subset_Z_of_union hnodes) z
              (fun a => indicator yz
                (restrictAssign (subset_YZ_of_union hnodes) a)) =
              marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz := by
          simpa [restrictAssignment] using
            (contextRestrictedSum_indicator_YZ_eq_marginalMass
              (G := G) (Var := Var) P X Y Z hnodes z yz hzy)
        have hci := hAlg xyz
        unfold conditionalExpectation
        rw [hprod, hX, hY]
        field_simp [hmZ_ne, mZ]
        ring_nf
        simpa [contextMass, hxyz_xz, hxyz_yz, hzxyz] using hci
      · have hprod :
            contextRestrictedSum P Z (subset_Z_of_union hnodes) z
              (fun a =>
                indicator xz (restrictAssign (subset_XZ_of_union hnodes) a) *
                indicator yz (restrictAssign (subset_YZ_of_union hnodes) a)) = 0 := by
          simpa [restrictAssignment] using
            (contextRestrictedSum_indicator_XZ_YZ_eq_zero_of_incompatible
              (G := G) (Var := Var) P X Y Z hnodes z xz yz hcompat)
        have hX :
            contextRestrictedSum P Z (subset_Z_of_union hnodes) z
              (fun a => indicator xz
                (restrictAssign (subset_XZ_of_union hnodes) a)) =
              marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes) xz := by
          simpa [restrictAssignment] using
            (contextRestrictedSum_indicator_XZ_eq_marginalMass
              (G := G) (Var := Var) P X Y Z hnodes z xz hzx)
        have hY :
            contextRestrictedSum P Z (subset_Z_of_union hnodes) z
              (fun a => indicator yz
                (restrictAssign (subset_YZ_of_union hnodes) a)) =
              marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz := by
          simpa [restrictAssignment] using
            (contextRestrictedSum_indicator_YZ_eq_marginalMass
              (G := G) (Var := Var) P X Y Z hnodes z yz hzy)
        have hyz_zero :
            marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz = 0 :=
          marginalMass_YZ_eq_zero_of_incompatible_CIAlg
            (G := G) (Var := Var) P hpos X Y Z hnodes hAlg z xz yz hzx hzy hcompat
        unfold conditionalExpectation
        rw [hprod, hX, hY, hyz_zero]
        simp
    · have hprod :
          contextRestrictedSum P Z (subset_Z_of_union hnodes) z
            (fun a =>
              indicator xz (restrictAssign (subset_XZ_of_union hnodes) a) *
              indicator yz (restrictAssign (subset_YZ_of_union hnodes) a)) = 0 := by
        simpa [restrictAssignment] using
          (contextRestrictedSum_indicator_XZ_YZ_eq_zero_of_YZ_context_ne
            (G := G) (Var := Var) P X Y Z hnodes z xz yz hzy)
      have hY :
          contextRestrictedSum P Z (subset_Z_of_union hnodes) z
            (fun a => indicator yz
              (restrictAssign (subset_YZ_of_union hnodes) a)) = 0 := by
        simpa [restrictAssignment, hzy] using
          (contextRestrictedSum_indicator_YZ_eq_if_marginalMass
            (G := G) (Var := Var) P X Y Z hnodes z yz)
      unfold conditionalExpectation
      rw [hprod, hY]
      simp
  · have hprod :
        contextRestrictedSum P Z (subset_Z_of_union hnodes) z
          (fun a =>
            indicator xz (restrictAssign (subset_XZ_of_union hnodes) a) *
            indicator yz (restrictAssign (subset_YZ_of_union hnodes) a)) = 0 := by
      simpa [restrictAssignment] using
        (contextRestrictedSum_indicator_XZ_YZ_eq_zero_of_XZ_context_ne
          (G := G) (Var := Var) P X Y Z hnodes z xz yz hzx)
    have hX :
        contextRestrictedSum P Z (subset_Z_of_union hnodes) z
          (fun a => indicator xz
            (restrictAssign (subset_XZ_of_union hnodes) a)) = 0 := by
      simpa [restrictAssignment, hzx] using
        (contextRestrictedSum_indicator_XZ_eq_if_marginalMass
          (G := G) (Var := Var) P X Y Z hnodes z xz)
    unfold conditionalExpectation
    rw [hprod, hX]
    simp

set_option maxHeartbeats 800000 in
private theorem CIExp_of_CIAlg_of_positive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) :
    CIAlg P X Y Z hnodes → CIExp P X Y Z hnodes := by
  classical
  intro hAlg z f g
  let hZ : Z ⊆ G.nodes := subset_Z_of_union hnodes
  let hXZ : X ∪ Z ⊆ G.nodes := subset_XZ_of_union hnodes
  let hYZ : Y ∪ Z ⊆ G.nodes := subset_YZ_of_union hnodes
  let rX : Assignment G Var → AssignOn Var (X ∪ Z) := fun a => restrictAssign hXZ a
  let rY : Assignment G Var → AssignOn Var (Y ∪ Z) := fun a => restrictAssign hYZ a
  let A : AssignOn Var (X ∪ Z) → ℝ :=
    fun xz => contextRestrictedSum P Z hZ z
      (fun a => indicator xz (rX a))
  let B : AssignOn Var (Y ∪ Z) → ℝ :=
    fun yz => contextRestrictedSum P Z hZ z
      (fun a => indicator yz (rY a))
  let C : AssignOn Var (X ∪ Z) → AssignOn Var (Y ∪ Z) → ℝ :=
    fun xz yz => contextRestrictedSum P Z hZ z
      (fun a => indicator xz (rX a) * indicator yz (rY a))
  let mZ : ℝ := contextMass P Z hZ z
  have hmZ_pos : 0 < mZ := by
    simpa [mZ, hZ] using
      (contextMass_pos_of_strictlyPositive
        (G := G) (Var := Var) P hpos Z (subset_Z_of_union hnodes) z)
  have hmZ_ne : mZ ≠ 0 := ne_of_gt hmZ_pos
  have hC :
      ∀ xz yz, C xz yz * mZ = A xz * B yz := by
    intro xz yz
    have hInd := conditionalExpectation_indicator_factor_of_CIAlg
      (G := G) (Var := Var) P hpos X Y Z hnodes hAlg z xz yz
    have hInd' :
        C xz yz / mZ = (A xz / mZ) * (B yz / mZ) := by
      simpa [conditionalExpectation, A, B, C, mZ, hZ, hXZ, hYZ, rX, rY] using hInd
    calc
      C xz yz * mZ = (C xz yz / mZ) * (mZ * mZ) := by
        field_simp [hmZ_ne]
      _ = ((A xz / mZ) * (B yz / mZ)) * (mZ * mZ) := by rw [hInd']
      _ = A xz * B yz := by
        field_simp [hmZ_ne]
  have hCRSf :
      contextRestrictedSum P Z hZ z (fun a => f (rX a)) =
        ∑ xz : AssignOn Var (X ∪ Z), f xz * A xz := by
    simpa [A, rX, one_mul] using
      (contextRestrictedSum_expand_by_indicator
        (G := G) (Var := Var) P Z hZ z rX (fun _ => (1 : ℝ)) f)
  have hCRSg :
      contextRestrictedSum P Z hZ z (fun a => g (rY a)) =
        ∑ yz : AssignOn Var (Y ∪ Z), g yz * B yz := by
    simpa [B, rY, one_mul] using
      (contextRestrictedSum_expand_by_indicator
        (G := G) (Var := Var) P Z hZ z rY (fun _ => (1 : ℝ)) g)
  have hinner :
      ∀ xz : AssignOn Var (X ∪ Z),
        contextRestrictedSum P Z hZ z
          (fun a => g (rY a) * indicator xz (rX a)) =
        ∑ yz : AssignOn Var (Y ∪ Z), g yz * C xz yz := by
    intro xz
    simpa [C, rX, rY, mul_comm, mul_left_comm, mul_assoc] using
      (contextRestrictedSum_expand_by_indicator
        (G := G) (Var := Var) P Z hZ z rY
        (fun a => indicator xz (rX a)) g)
  have hCRSfg :
      contextRestrictedSum P Z hZ z
        (fun a => f (rX a) * g (rY a)) =
        ∑ xz : AssignOn Var (X ∪ Z),
          f xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * C xz yz) := by
    have hstep :
        contextRestrictedSum P Z hZ z
          (fun a => f (rX a) * g (rY a)) =
        ∑ xz : AssignOn Var (X ∪ Z), f xz *
          contextRestrictedSum P Z hZ z
            (fun a => g (rY a) * indicator xz (rX a)) := by
      simpa [rX, rY, mul_comm, mul_left_comm, mul_assoc] using
        (contextRestrictedSum_expand_by_indicator
          (G := G) (Var := Var) P Z hZ z rX
          (fun a => g (rY a)) f)
    rw [hstep]
    refine Finset.sum_congr rfl ?_
    intro xz hxz
    rw [hinner xz]
  unfold conditionalExpectation
  have hmain :
      contextRestrictedSum P Z hZ z (fun a => f (rX a) * g (rY a)) * mZ =
        contextRestrictedSum P Z hZ z (fun a => f (rX a)) *
          contextRestrictedSum P Z hZ z (fun a => g (rY a)) := by
    rw [hCRSfg, hCRSf, hCRSg]
    calc
      (∑ xz : AssignOn Var (X ∪ Z),
          f xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * C xz yz)) * mZ
          =
        ∑ xz : AssignOn Var (X ∪ Z),
          f xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * (C xz yz * mZ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro xz hxz
        calc
          (f xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * C xz yz)) * mZ
              =
            f xz * ((∑ yz : AssignOn Var (Y ∪ Z), g yz * C xz yz) * mZ) := by ring
          _ = f xz *
              (∑ yz : AssignOn Var (Y ∪ Z), (g yz * C xz yz) * mZ) := by
            rw [Finset.sum_mul]
          _ = f xz *
              (∑ yz : AssignOn Var (Y ∪ Z), g yz * (C xz yz * mZ)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro yz hyz
            ring
      _ =
        ∑ xz : AssignOn Var (X ∪ Z),
          f xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * (A xz * B yz)) := by
        refine Finset.sum_congr rfl ?_
        intro xz hxz
        congr 1
        refine Finset.sum_congr rfl ?_
        intro yz hyz
        rw [hC xz yz]
      _ =
        (∑ xz : AssignOn Var (X ∪ Z), f xz * A xz) *
          (∑ yz : AssignOn Var (Y ∪ Z), g yz * B yz) := by
        exact calc
          (∑ xz : AssignOn Var (X ∪ Z),
            f xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * (A xz * B yz)))
              =
            ∑ xz : AssignOn Var (X ∪ Z),
              (f xz * A xz) *
                (∑ yz : AssignOn Var (Y ∪ Z), g yz * B yz) := by
            refine Finset.sum_congr rfl ?_
            intro xz hxz
            have hinner2 :
                (∑ yz : AssignOn Var (Y ∪ Z), g yz * (A xz * B yz))
                  = A xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * B yz) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro yz hyz
              ring
            calc
              f xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * (A xz * B yz))
                  = f xz * (A xz * (∑ yz : AssignOn Var (Y ∪ Z), g yz * B yz)) := by
                rw [hinner2]
              _ = (f xz * A xz) *
                  (∑ yz : AssignOn Var (Y ∪ Z), g yz * B yz) := by
                ring
          _ =
            (∑ xz : AssignOn Var (X ∪ Z), f xz * A xz) *
              (∑ yz : AssignOn Var (Y ∪ Z), g yz * B yz) := by
            rw [Finset.sum_mul]
  exact show
    contextRestrictedSum P Z hZ z (fun a => f (rX a) * g (rY a)) / mZ =
      contextRestrictedSum P Z hZ z (fun a => f (rX a)) / mZ *
        (contextRestrictedSum P Z hZ z (fun a => g (rY a)) / mZ) from
  calc
    contextRestrictedSum P Z hZ z (fun a => f (rX a) * g (rY a)) / mZ
        =
      (contextRestrictedSum P Z hZ z (fun a => f (rX a) * g (rY a)) * mZ) /
        (mZ * mZ) := by
          field_simp [hmZ_ne]
    _ =
      (contextRestrictedSum P Z hZ z (fun a => f (rX a)) *
        contextRestrictedSum P Z hZ z (fun a => g (rY a))) /
        (mZ * mZ) := by
          rw [hmain]
    _ =
      contextRestrictedSum P Z hZ z (fun a => f (rX a)) / mZ *
        (contextRestrictedSum P Z hZ z (fun a => g (rY a)) / mZ) := by
          field_simp [hmZ_ne]

private theorem contextRestrictedSum_indicator_XZ_YZ_eq_marginalMass
    (P : FinitePMF (Assignment G Var))
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes)
    (xyz : AssignOn Var (X ∪ Y ∪ Z)) :
    contextRestrictedSum P Z (subset_Z_of_union hnodes)
        (restrictAssign (subset_Z_of_XYZ X Y Z) xyz)
        (fun a =>
          indicator (restrictAssign (subset_XZ_of_XYZ X Y Z) xyz)
            (restrictAssignment (subset_XZ_of_union hnodes) a) *
          indicator (restrictAssign (subset_YZ_of_XYZ X Y Z) xyz)
            (restrictAssignment (subset_YZ_of_union hnodes) a)) =
      marginalMass P (X ∪ Y ∪ Z) hnodes xyz := by
  classical
  unfold contextRestrictedSum marginalMass indicator
  refine Finset.sum_congr rfl ?_
  intro a ha
  by_cases hfull : restrictAssignment hnodes a = xyz
  · have hXZ :
        restrictAssignment (subset_XZ_of_union hnodes) a =
          restrictAssign (subset_XZ_of_XYZ X Y Z) xyz :=
      ((restrictAssignment_XYZ_eq_iff_XZ_YZ
        (G := G) (Var := Var) X Y Z hnodes a xyz).1 hfull).1
    have hYZ :
        restrictAssignment (subset_YZ_of_union hnodes) a =
          restrictAssign (subset_YZ_of_XYZ X Y Z) xyz :=
      ((restrictAssignment_XYZ_eq_iff_XZ_YZ
        (G := G) (Var := Var) X Y Z hnodes a xyz).1 hfull).2
    have hZ : restrictAssignment (subset_Z_of_union hnodes) a =
        restrictAssign (subset_Z_of_XYZ X Y Z) xyz := by
      calc
        restrictAssignment (subset_Z_of_union hnodes) a =
            restrictAssign (subset_Z_of_XYZ X Y Z)
              (restrictAssignment hnodes a) := by
              exact (restrictAssignment_comp
                (G := G) (Var := Var)
                (hST := subset_Z_of_XYZ X Y Z)
                (hT := hnodes)
                (hS := subset_Z_of_union hnodes) a).symm
        _ = restrictAssign (subset_Z_of_XYZ X Y Z) xyz := by rw [hfull]
    simp [hfull, hXZ, hYZ, hZ]
  · by_cases hZ : restrictAssignment (subset_Z_of_union hnodes) a =
        restrictAssign (subset_Z_of_XYZ X Y Z) xyz
    · by_cases hXZ :
        restrictAssignment (subset_XZ_of_union hnodes) a =
          restrictAssign (subset_XZ_of_XYZ X Y Z) xyz
      · by_cases hYZ :
          restrictAssignment (subset_YZ_of_union hnodes) a =
            restrictAssign (subset_YZ_of_XYZ X Y Z) xyz
        · have hfull' : restrictAssignment hnodes a = xyz :=
            (restrictAssignment_XYZ_eq_iff_XZ_YZ
              (G := G) (Var := Var) X Y Z hnodes a xyz).2 ⟨hXZ, hYZ⟩
          exact False.elim (hfull hfull')
        · simp [hfull, hZ, hXZ, hYZ]
      · simp [hfull, hZ, hXZ]
    · simp [hfull, hZ]

private theorem CIAlg_of_CIExp_of_positive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) :
    CIExp P X Y Z hnodes → CIAlg P X Y Z hnodes := by
  classical
  intro hExp xyz
  let z : AssignOn Var Z := restrictAssign (subset_Z_of_XYZ X Y Z) xyz
  let xz : AssignOn Var (X ∪ Z) := restrictAssign (subset_XZ_of_XYZ X Y Z) xyz
  let yz : AssignOn Var (Y ∪ Z) := restrictAssign (subset_YZ_of_XYZ X Y Z) xyz
  have hzx : restrictAssign (subset_Z_of_XZ X Z) xz = z := by
    simpa [xz, z] using
      (restrict_XZ_then_Z_eq_restrict_XYZ_then_Z
        (Var := Var) X Y Z xyz)
  have hzy : restrictAssign (subset_Z_of_YZ Y Z) yz = z := by
    simpa [yz, z] using
      (restrict_YZ_then_Z_eq_restrict_XYZ_then_Z
        (Var := Var) X Y Z xyz)
  have htest := hExp z (indicator xz) (indicator yz)
  have hXYZ :
      contextRestrictedSum P Z (subset_Z_of_union hnodes) z
          (fun a =>
            indicator xz (restrictAssign (subset_XZ_of_union hnodes) a) *
            indicator yz (restrictAssign (subset_YZ_of_union hnodes) a)) =
        marginalMass P (X ∪ Y ∪ Z) hnodes xyz := by
    simpa [restrictAssignment, xz, yz, z] using
      (contextRestrictedSum_indicator_XZ_YZ_eq_marginalMass
        (G := G) (Var := Var) P X Y Z hnodes xyz)
  have hXZ :
      contextRestrictedSum P Z (subset_Z_of_union hnodes) z
          (fun a => indicator xz
            (restrictAssign (subset_XZ_of_union hnodes) a)) =
        marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes) xz :=
    by
      simpa [restrictAssignment] using
        (contextRestrictedSum_indicator_XZ_eq_marginalMass
          (G := G) (Var := Var) P X Y Z hnodes z xz hzx)
  have hYZ :
      contextRestrictedSum P Z (subset_Z_of_union hnodes) z
          (fun a => indicator yz
            (restrictAssign (subset_YZ_of_union hnodes) a)) =
        marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz :=
    by
      simpa [restrictAssignment] using
        (contextRestrictedSum_indicator_YZ_eq_marginalMass
          (G := G) (Var := Var) P X Y Z hnodes z yz hzy)
  have hmass_pos : 0 < contextMass P Z (subset_Z_of_union hnodes) z :=
    contextMass_pos_of_strictlyPositive (G := G) (Var := Var)
      P hpos Z (subset_Z_of_union hnodes) z
  have hmass_ne : contextMass P Z (subset_Z_of_union hnodes) z ≠ 0 :=
    ne_of_gt hmass_pos
  unfold conditionalExpectation at htest
  rw [hXYZ, hXZ, hYZ] at htest
  have hcleared :
      marginalMass P (X ∪ Y ∪ Z) hnodes xyz *
          contextMass P Z (subset_Z_of_union hnodes) z =
        marginalMass P (X ∪ Z) (subset_XZ_of_union hnodes) xz *
          marginalMass P (Y ∪ Z) (subset_YZ_of_union hnodes) yz := by
    field_simp [hmass_ne] at htest
    ring_nf at htest ⊢
    exact htest
  simpa [CIAlg, xz, yz, z] using hcleared

-- Proved finite-assignment bridge: `CIExp` ↔ `CIAlg` under positivity.
theorem CIExp_iff_CIAlg_of_positive
    (P : FinitePMF (Assignment G Var)) (hpos : StrictlyPositive P)
    (X Y Z : Finset ℕ) (hnodes : X ∪ Y ∪ Z ⊆ G.nodes) :
    CIExp P X Y Z hnodes ↔ CIAlg P X Y Z hnodes := by
  constructor
  · exact CIAlg_of_CIExp_of_positive (G := G) (Var := Var) P hpos X Y Z hnodes
  · exact CIExp_of_CIAlg_of_positive (G := G) (Var := Var) P hpos X Y Z hnodes

-- Symmetry of algebraic CI.
theorem ci_symm (P : FinitePMF (Assignment G Var)) {X Y Z : Finset ℕ} :
    CIAlgOnNodes P X Y Z → CIAlgOnNodes P Y X Z := by
  rintro ⟨hnodes, hXY⟩
  let hnodes' : Y ∪ X ∪ Z ⊆ G.nodes := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hnodes
  refine ⟨hnodes', ?_⟩
  let hswapYX : ∀ n, n ∈ Y ∪ X ∪ Z ↔ n ∈ X ∪ Y ∪ Z := by
    intro n
    simp [Finset.union_left_comm, Finset.union_comm]
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
