import CausalQIF.Graph.Moralization

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Trail Inductive

The core trail syntax linking two vertices in a DAG via forward/backward edges,
together with structural helpers (`toList`, `nodes`, `append`).
-/

variable {V : Type} [DecidableEq V] [Fintype V]

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

end

end CausalQIF.DSeparation
