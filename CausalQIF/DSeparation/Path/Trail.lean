import CausalQIF.Graph.Moralization

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Trails and Local Blocking

Core trail syntax, triple predicates, local triple blocking.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

def hasTriple (xs : List V) (a b c : V) : Prop :=
  ∃ pre post : List V, xs = pre ++ a :: b :: c :: post

inductive Trail (G : Graph.DAG V) : V → V → Type where
  | nil (v : V) : Trail G v v
  | forward {u w v : V} (h : G.hasEdge u w) (tail : Trail G w v) : Trail G u v
  | backward {u w v : V} (h : G.hasEdge w u) (tail : Trail G w v) : Trail G u v

namespace Trail

variable {V : Type} [DecidableEq V] [Fintype V]

def toList {G : Graph.DAG V} : {u v : V} → Trail G u v → List V
  | _, _, nil v => [v]
  | u, _, forward (u := _) (w := _) (v := _) _ tail => u :: toList tail
  | u, _, backward (u := _) (w := _) (v := _) _ tail => u :: toList tail

def nodes {G : Graph.DAG V} {u v : V} (t : Trail G u v) : Finset V :=
  t.toList.toFinset

@[simp]
lemma mem_nodes {G : Graph.DAG V} {u v a : V} {t : Trail G u v} :
    a ∈ t.nodes ↔ a ∈ t.toList := by
  simp [nodes]

lemma target_mem_graph_nodes_of_source_mem {G : Graph.DAG V} {u v : V}
    (t : Trail G u v) (hu : u ∈ G.nodes) :
    v ∈ G.nodes := by
  induction t with
  | nil _ =>
      exact hu
  | forward h tail ih =>
      exact ih (G.edges_subset h).2
  | backward h tail ih =>
      exact ih (G.edges_subset h).1

def append {G : Graph.DAG V} {u v w : V} (p : Trail G u v) (q : Trail G v w) :
    Trail G u w :=
  match p with
  | nil _ => q
  | forward h tail => forward h (tail.append q)
  | backward h tail => backward h (tail.append q)

lemma exists_ofReachableForward {G : Graph.DAG V} {u v : V}
    (h : Graph.reachable G u v) : Nonempty (Trail G u v) := by
  induction h with
  | refl =>
      exact ⟨Trail.nil u⟩
  | tail _ hstep ih =>
      rcases ih with ⟨tail⟩
      exact ⟨tail.append (Trail.forward hstep (Trail.nil _))⟩

lemma exists_ofReachableBackward {G : Graph.DAG V} {u v : V}
    (h : Graph.reachable G u v) : Nonempty (Trail G v u) := by
  induction h with
  | refl =>
      exact ⟨Trail.nil u⟩
  | tail _ hstep ih =>
      rcases ih with ⟨tail⟩
      exact ⟨(Trail.backward hstep (Trail.nil _)).append tail⟩

end Trail

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

end

end CausalQIF.DSeparation
