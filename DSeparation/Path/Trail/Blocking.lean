import CausalQIF.DSeparation.Path.Trail.Basic
import CausalQIF.DSeparation.Path.Trail.Triple

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Trail Blocking and D-Separation

List-level `hasTriple` helper, the trail-blocking predicate `trailBlocked`, the
trail-level `Trail.isBlocked` / `Trail.startOpen` view, the top-level
`dSeparates` predicate, and the head-vs-tail blocking lemmas used in the
Bayes-ball ⇄ trail bridge.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

def hasTriple (xs : List V) (a b c : V) : Prop :=
  ∃ pre post : List V, xs = pre ++ a :: b :: c :: post

def trailBlocked (G : Graph.DAG V) (Z : Finset V) (xs : List V) : Prop :=
  ∃ a b c : V, hasTriple xs a b c ∧ tripleBlocked G Z a b c

def Trail.isBlocked {G : Graph.DAG V} {u v : V} (Z : Finset V) (t : Trail G u v) : Prop :=
  trailBlocked G Z t.toList

def Trail.startOpen {G : Graph.DAG V} {u v : V} (Z : Finset V) (init_dir : TrailDir)
    (t : Trail G u v) : Prop :=
  match t with
  | Trail.nil _ => True
  | Trail.forward (u := u) _ _ =>
      ¬ directionalTripleBlocked G Z u init_dir TrailDir.into
  | Trail.backward (u := u) _ _ =>
      ¬ directionalTripleBlocked G Z u init_dir TrailDir.outOf

def dSeparates (G : Graph.DAG V) (X Y Z : Finset V) : Prop :=
  ∀ x, x ∈ X → ∀ y, y ∈ Y → ∀ t : Trail G x y, t.isBlocked Z

def disjointSets (X Y Z : Finset V) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z

omit [DecidableEq V] [Fintype V] in
lemma hasTriple.cons {xs : List V} {a b c x : V}
    (h : hasTriple xs a b c) :
    hasTriple (x :: xs) a b c := by
  rcases h with ⟨pre, post, hxs⟩
  exact ⟨x :: pre, post, by simp [hxs, List.cons_append]⟩

lemma hasTriple.head_of_trail {G : Graph.DAG V} {a b c v : V} (t : Trail G c v) :
    hasTriple (a :: b :: t.toList) a b c := by
  cases t with
  | nil v =>
      exact ⟨[], [], by simp [Trail.toList]⟩
  | forward h tail =>
      exact ⟨[], tail.toList, by simp [Trail.toList]⟩
  | backward h tail =>
      exact ⟨[], tail.toList, by simp [Trail.toList]⟩

lemma not_trailBlocked_tail_of_not_trailBlocked_cons {G : Graph.DAG V} {Z : Finset V}
    {xs : List V} {x : V}
    (h : ¬ trailBlocked G Z (x :: xs)) :
    ¬ trailBlocked G Z xs := by
  intro htail
  rcases htail with ⟨a, b, c, htriple, hblocked⟩
  exact h ⟨a, b, c, hasTriple.cons htriple, hblocked⟩

lemma trailBlocked_of_head_tripleBlocked {G : Graph.DAG V} {Z : Finset V}
    {a b c : V} {xs : List V}
    (h : tripleBlocked G Z a b c) :
    trailBlocked G Z (a :: b :: c :: xs) :=
  ⟨a, b, c, ⟨[], xs, rfl⟩, h⟩

lemma not_tripleBlocked_head_of_not_trailBlocked {G : Graph.DAG V} {Z : Finset V}
    {a b c : V} {xs : List V}
    (h : ¬ trailBlocked G Z (a :: b :: c :: xs)) :
    ¬ tripleBlocked G Z a b c := by
  intro htriple
  exact h (trailBlocked_of_head_tripleBlocked htriple)

lemma trailBlocked_of_head_tripleBlocked_trail {G : Graph.DAG V} {Z : Finset V}
    {a b c v : V} {t : Trail G c v}
    (h : tripleBlocked G Z a b c) :
    trailBlocked G Z (a :: b :: t.toList) :=
  ⟨a, b, c, hasTriple.head_of_trail t, h⟩

lemma not_tripleBlocked_head_of_not_trailBlocked_trail {G : Graph.DAG V} {Z : Finset V}
    {a b c v : V} {t : Trail G c v}
    (h : ¬ trailBlocked G Z (a :: b :: t.toList)) :
    ¬ tripleBlocked G Z a b c := by
  intro htriple
  exact h (trailBlocked_of_head_tripleBlocked_trail htriple)

end

end CausalQIF.DSeparation
