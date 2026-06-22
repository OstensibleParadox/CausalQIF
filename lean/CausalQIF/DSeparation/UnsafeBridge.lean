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
  intro h hnodes'
  let hnodes : X ∪ Y ∪ Z ⊆ G.nodes := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hnodes'
  let hswapYX : ∀ n, n ∈ Y ∪ X ∪ Z ↔ n ∈ X ∪ Y ∪ Z := by
    intro n
    simp [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
  have hXY := h hnodes
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
      restrictAssign (subset_XZ_of_union (X := X) (Y := Y) (Z := Z) hnodes) xyz =
        restrictAssign (subset_XZ_of_XYZ (X := X) (Y := Y) (Z := Z)) xyz' := by
    have hTU : X ∪ Z ⊆ X ∪ Y ∪ Z :=
      subset_XZ_of_union (X := X) (Y := Y) (Z := Z) hnodes
    simpa using (reindex_restrict (G := G) (Var := Var)
      (hST := hswapYX)
      (hSU := subset_XZ_of_XYZ (X := X) (Y := Y) (Z := Z))
      (hTU := hTU)
      (a := xyz'))
  have hYZ :
      restrictAssign (subset_YZ_of_union (X := X) (Y := Y) (Z := Z) hnodes) xyz =
        restrictAssign (subset_YZ_of_XYZ (X := X) (Y := Y) (Z := Z)) xyz' := by
    simpa using (reindex_restrict (G := G) (Var := Var)
      (hST := hswapYX)
      (hSU := subset_YZ_of_XYZ (X := Y) (Y := X) (Z := Z))
      (hTU := subset_YZ_of_union (X := X) (Y := Y) (Z := Z) hnodes)
      (a := xyz'))
  have hZ :
      restrictAssign (subset_Z_of_XYZ X Y Z) xyz =
        restrictAssign (subset_Z_of_XYZ Y X Z) xyz' := by
    simpa using (reindex_restrict (G := G) (Var := Var)
      (hST := hswapYX)
      (hSU := subset_Z_of_XYZ Y X Z)
      (hTU := subset_Z_of_union (X := X) (Y := Y) (Z := Z) hnodes)
      (a := xyz'))
  -- Goal-side rearrangement of set unions is handled by `simp`.
  simpa [CIAlg, xyz, hmass, hXZ, hYZ, hZ,
    Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using h1

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
theorem isMarkovChain_of_CIExp_project3 {G : DAG} {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : PositiveMarkovModel G (Tuple3Var α β γ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ) ⊆ G.nodes)
    (hci : CIExp M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1} : Finset ℕ) hnodes) :
    UnsafeIsMarkovChain (project3PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
  classical
  intro a b c
  let hzc : AssignOn (Tuple3Var α β γ) ({1} : Finset ℕ) := by
    intro x
    have hx : x.1 = 1 := Finset.mem_singleton.mp x.2
    simpa [hx, Tuple3Var] using b
  let xz0 : {n // n ∈ ({0} : Finset ℕ) ∪ ({1} : Finset ℕ)} := ⟨0, by simp⟩
  let xz0' : {n // n ∈ ({0} : Finset ℕ) ∪ ({1} : Finset ℕ)} := ⟨0, by simp⟩
  let fy0 : {n // n ∈ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ)} := ⟨2, by simp⟩
  let fy1 : {n // n ∈ ({2} : Finset ℕ) ∪ ({1} : Finset ℕ)} := ⟨1, by simp⟩
  let fxz : AssignOn (Tuple3Var α β γ) (({0} : Finset ℕ) ∪ ({1} : Finset ℕ)) → ℝ := by
    intro xz
    exact if xz xz0 = a then (1 : ℝ) else 0
  let fyz : AssignOn (Tuple3Var α β γ) (({2} : Finset ℕ) ∪ ({1} : Finset ℕ)) → ℝ := by
    intro yz
    exact if yz fy0 = c ∧ yz fy1 = b then (1 : ℝ) else 0
  have hci' := hci hzc fxz fyz
  let hZnodes3 : ({1} : Finset ℕ) ⊆ G.nodes :=
    subset_Z_of_union (X := ({0} : Finset ℕ)) (Y := ({2} : Finset ℕ)) (Z := ({1} : Finset ℕ)) hnodes
  let Q3 : FinitePMF (α × β × γ) :=
    project3PMF M (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))
  have hci'' :
      Q3.pmf (a, b, c) * (∑ a' : α, ∑ c' : γ, Q3.pmf (a', b, c')) =
        (∑ c' : γ, Q3.pmf (a, b, c')) * (∑ a' : α, Q3.pmf (a', b, c)) := by
    have hpos : 0 < contextMass M.P ({1} : Finset ℕ) hZnodes3 hzc :=
      contextMass_pos_of_strictlyPositive (G := G) (Var := Tuple3Var α β γ) M.P M.positive
        ({1} : Finset ℕ)
        hZnodes3
        hzc
    have hci''':
        (∑ x : Assignment G (Tuple3Var α β γ),
          if restrictAssignment hZnodes3 x = hzc then
            M.P.pmf x * (fxz (restrictAssign (subset_XZ_of_union (X := ({0} : Finset ℕ))
              (Y := ({2} : Finset ℕ)) (Z := ({1} : Finset ℕ)) hnodes) x) *
              fyz (restrictAssign (subset_YZ_of_union (X := ({0} : Finset ℕ))
                (Y := ({2} : Finset ℕ)) (Z := ({1} : Finset ℕ)) hnodes) x)) else 0) *
            contextMass M.P ({1} : Finset ℕ)
              hZnodes3 hzc =
        (∑ x : Assignment G (Tuple3Var α β γ),
          if restrictAssignment hZnodes3 x = hzc then
            M.P.pmf x * fxz (restrictAssign (subset_XZ_of_union (X := ({0} : Finset ℕ))
              (Y := ({2} : Finset ℕ)) (Z := ({1} : Finset ℕ)) hnodes) x) else 0) *
        (∑ x : Assignment G (Tuple3Var α β γ),
          if restrictAssignment hZnodes3 x = hzc then
            M.P.pmf x * fyz (restrictAssign (subset_YZ_of_union (X := ({0} : Finset ℕ))
              (Y := ({2} : Finset ℕ)) (Z := ({1} : Finset ℕ)) hnodes) x) else 0) := by
      have hciMul := hci'
      field_simp [contextMass, conditionalExpectation, contextRestrictedSum, hpos.ne', hci']
      exact hciMul
    simpa [UnsafeIsMarkovChain, conditionalExpectation, contextRestrictedSum, contextMass,
      FinitePMF.map, project3PMF, Q3, restrictAssign, hzc, fxz, fyz, Tuple3Var] using hci'''
  simpa [Q3] using hci''

-- Pending audit entry: four-variable projection bridge.
theorem condMarkov_of_CIExp_project4 {G : DAG} {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (M : PositiveMarkovModel G (Tuple4Var α β γ δ))
    (hnodes : ({0} : Finset ℕ) ∪ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ) ⊆ G.nodes)
    (hci : CIExp M.P ({0} : Finset ℕ) ({2} : Finset ℕ) ({1, 3} : Finset ℕ) hnodes) :
    condMarkov (project4PMF M
      (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))) := by
  classical
  intro a b c d
  let hzw : AssignOn (Tuple4Var α β γ δ) ({1, 3} : Finset ℕ) := by
    intro x
    have hx' : x.1 = 1 ∨ x.1 = 3 := by
      rcases Finset.mem_insert.mp x.2 with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Finset.mem_singleton.mp hx)
    by_cases hx1 : x.1 = 1
    · simpa [hx1, Tuple4Var] using b
    · have hx3 : x.1 = 3 := by
        rcases hx' with h | h
        · exact (hx1 h).elim
        · exact h
      simpa [hx3, Tuple4Var] using d
  let x0 : {n // n ∈ ({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)} := ⟨0, by simp⟩
  let y1 : {n // n ∈ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)} := ⟨1, by simp⟩
  let y3 : {n // n ∈ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)} := ⟨3, by simp⟩
  let z2 : {n // n ∈ ({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)} := ⟨2, by simp⟩
  let fxy : AssignOn (Tuple4Var α β γ δ) (({0} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)) → ℝ := by
    intro xz
    exact if xz x0 = a then (1 : ℝ) else 0
  let fyz : AssignOn (Tuple4Var α β γ δ) (({2} : Finset ℕ) ∪ ({1, 3} : Finset ℕ)) → ℝ := by
    intro yz
    exact if yz z2 = c ∧ yz y1 = b ∧ yz y3 = d then (1 : ℝ) else 0
  have hci' := hci hzw fxy fyz
  let hZnodes4 : ({1, 3} : Finset ℕ) ⊆ G.nodes :=
    subset_Z_of_union (X := ({0} : Finset ℕ)) (Y := ({2} : Finset ℕ)) (Z := ({1, 3} : Finset ℕ)) hnodes
  let Q4 : FinitePMF (α × β × γ × δ) :=
    project4PMF M (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp)) (hnodes (by simp))
  have hci'' :
      Q4.pmf (a, b, c, d) * (∑ y : β, ∑ z : γ, Q4.pmf (a, y, z, d)) =
        (∑ z : γ, Q4.pmf (a, b, z, d)) * (∑ a' : α, Q4.pmf (a', b, c, d)) := by
    simpa [condMarkov, conditionalExpectation, contextRestrictedSum, contextMass, FinitePMF.map,
      project4PMF, Q4, restrictAssign] using hci'
    -- convert from conditional-expectation factorization to explicit marginals
  have hci''' :
      Q4.pmf (a, b, c, d) * (∑ y : β, ∑ z : γ, Q4.pmf (a, y, z, d)) =
        (∑ z : γ, Q4.pmf (a, b, z, d)) * (∑ x : α, Q4.pmf (x, b, c, d)) := by
    have hpos : 0 < contextMass M.P ({1, 3} : Finset ℕ) hZnodes4 hzw :=
      contextMass_pos_of_strictlyPositive (G := G) (Var := Tuple4Var α β γ δ) M.P M.positive
        ({1, 3} : Finset ℕ)
        hZnodes4
        hzw
    have hciMul :
        (∑ x : Assignment G (Tuple4Var α β γ δ),
          if restrictAssignment hZnodes4 x = hzw then
            M.P.pmf x * (fxy (restrictAssign (subset_XZ_of_union (X := ({0} : Finset ℕ))
              (Y := ({2} : Finset ℕ)) (Z := ({1, 3} : Finset ℕ)) hnodes) x) *
              fyz (restrictAssign (subset_YZ_of_union (X := ({0} : Finset ℕ))
                (Y := ({2} : Finset ℕ)) (Z := ({1, 3} : Finset ℕ)) hnodes) x)) else 0) *
            contextMass M.P ({1, 3} : Finset ℕ)
              hZnodes4 hzw =
        (∑ x : Assignment G (Tuple4Var α β γ δ),
          if restrictAssignment hZnodes4 x = hzw then
            M.P.pmf x * fxy (restrictAssign (subset_XZ_of_union (X := ({0} : Finset ℕ))
              (Y := ({2} : Finset ℕ)) (Z := ({1, 3} : Finset ℕ)) hnodes) x) else 0) *
        (∑ x : Assignment G (Tuple4Var α β γ δ),
          if restrictAssignment hZnodes4 x = hzw then
            M.P.pmf x * fyz (restrictAssign (subset_YZ_of_union (X := ({0} : Finset ℕ))
              (Y := ({2} : Finset ℕ)) (Z := ({1, 3} : Finset ℕ)) hnodes) x) else 0) := by
      have hciMul' := hci'
      field_simp [contextMass, conditionalExpectation, contextRestrictedSum, hpos.ne', hciMul']
      exact hciMul'
    simpa [condMarkov, conditionalExpectation, contextRestrictedSum, contextMass, FinitePMF.map,
      project4PMF, Q4, restrictAssign, hzw, fxy, fyz, Tuple4Var, marginalXYWMass,
      marginalYWMass, marginalYZWMass] using hciMul
  -- goal side has `condMarkov` marginals
  simpa [condMarkov, Q4] using hci'''

end AssignmentSemantics

end

end CausalQIF.UnsafeBridge
