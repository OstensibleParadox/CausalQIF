import CausalQIF.Graph.Moralization

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Triple Blocking Predicates

Collider/non-collider triple predicates and the direction-tagged variant used
by the Bayes-ball walker, plus their equivalence under matching edge orientations.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

def tripleCollider (G : Graph.DAG V) (a b c : V) : Prop :=
  G.hasEdge a b ∧ G.hasEdge c b

def tripleBlocked (G : Graph.DAG V) (Z : Finset V) (a b c : V) : Prop :=
  (¬ tripleCollider G a b c ∧ b ∈ Z) ∨
    (tripleCollider G a b c ∧ Disjoint ({b} ∪ Graph.descendants G b) Z)

inductive TrailDir where
  | into
  | outOf
  deriving DecidableEq

namespace TrailDir

variable {V : Type} [DecidableEq V] [Fintype V]

def edgeIntoCurrent (G : Graph.DAG V) (prev curr : V) : TrailDir → Prop
  | into => G.hasEdge prev curr
  | outOf => G.hasEdge curr prev

def colliderAtCurrent (arrival departure : TrailDir) : Prop :=
  arrival = into ∧ departure = outOf

end TrailDir

def directionalTripleBlocked (G : Graph.DAG V) (Z : Finset V) (b : V)
    (arrival departure : TrailDir) : Prop :=
  (¬ TrailDir.colliderAtCurrent arrival departure ∧ b ∈ Z) ∨
    (TrailDir.colliderAtCurrent arrival departure ∧
      Disjoint ({b} ∪ Graph.descendants G b) Z)

/-- Direction-only blocking agrees with the usual triple-blocking predicate
when the two directed edge orientations match the adjacent trail steps. -/
lemma directionalTripleBlocked_iff_tripleBlocked {G : Graph.DAG V} {Z : Finset V}
    {a b c : V} {arrival departure : TrailDir}
    (hab : TrailDir.edgeIntoCurrent G a b arrival)
    (hbc : TrailDir.edgeIntoCurrent G b c departure) :
    directionalTripleBlocked G Z b arrival departure ↔ tripleBlocked G Z a b c := by
  cases arrival <;> cases departure
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_cb : ¬ G.hasEdge c b := G.not_hasEdge_reverse_of_hasEdge hbc
    have hnot : ¬ tripleCollider G a b c := fun hcoll => hnot_cb hcoll.2
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hnot]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hcoll : tripleCollider G a b c := ⟨hab, hbc⟩
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hcoll]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_ab : ¬ G.hasEdge a b := G.not_hasEdge_reverse_of_hasEdge hab
    have hnot : ¬ tripleCollider G a b c := fun hcoll => hnot_ab hcoll.1
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hnot]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_ab : ¬ G.hasEdge a b := G.not_hasEdge_reverse_of_hasEdge hab
    have hnot : ¬ tripleCollider G a b c := fun hcoll => hnot_ab hcoll.1
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hnot]

end

end CausalQIF.DSeparation
