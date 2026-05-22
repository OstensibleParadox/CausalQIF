import CausalQIF.Graph.Moralization

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Trace-Synthesis Graph Lemmas

Small graph facts used by the reverse trace-synthesis normalization argument.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

/--
If `w` is ancestral to `X ∪ Y ∪ Z` but neither `w` nor any descendant of `w`
lies in `Z`, then the ancestral target reached from `w` must lie in `X` or `Y`.
-/
lemma ancestor_escape {G : Graph.DAG V} {X Y Z : Finset V} {w : V}
    (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hZ : Disjoint ({w} ∪ Graph.descendants G w) Z) :
    (∃ x, x ∈ X ∧ Graph.reachable G w x) ∨
      (∃ y, y ∈ Y ∧ Graph.reachable G w y) := by
  classical
  rcases Finset.mem_biUnion.mp hw with ⟨s, hsS, hws⟩
  have hwG : w ∈ G.nodes := (Finset.mem_filter.mp hws).1
  have hwsReach : Graph.reachable G w s := (Finset.mem_filter.mp hws).2
  rcases Finset.mem_union.mp hsS with hsXY | hsZ
  · rcases Finset.mem_union.mp hsXY with hsX | hsY
    · exact Or.inl ⟨s, hsX, hwsReach⟩
    · exact Or.inr ⟨s, hsY, hwsReach⟩
  · have hsCone : s ∈ ({w} ∪ Graph.descendants G w) := by
      by_cases hsw : s = w
      · subst s
        simp
      · exact Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr
            ⟨Graph.DAG.target_mem_nodes_of_reachable hwsReach hwG, hsw, hwsReach⟩
    exact False.elim ((Finset.disjoint_left.mp hZ) hsCone hsZ)

/-- The child of a bad collider survives conditioning on `Z`. -/
lemma bad_child_survives {G : Graph.DAG V} {X Y Z : Finset V} {w : V}
    (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hZ : Disjoint ({w} ∪ Graph.descendants G w) Z) :
    w ∈ G.dSeparationGraphNodes X Y Z := by
  apply Graph.DAG.mem_dSeparationGraphNodes_of_ancestor_not_mem hw
  intro h
  exact Finset.disjoint_left.mp hZ (by simp) h

/-- Nodes on an escape path from a bad collider survive conditioning on `Z`. -/
lemma escape_path_survives {G : Graph.DAG V} {X Y Z : Finset V} {w target : V}
    (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z))
    (hZ : Disjoint ({w} ∪ Graph.descendants G w) Z)
    (htarget : target ∈ X ∪ Y) :
    ∀ n, Graph.reachable G w n → Graph.reachable G n target →
      n ∈ G.dSeparationGraphNodes X Y Z := by
  classical
  intro n hwn hnt
  apply Graph.DAG.mem_dSeparationGraphNodes_of_ancestor_not_mem
  · have hw_node : w ∈ G.nodes := by
      rcases Finset.mem_biUnion.mp hw with ⟨s, hs, hw_anc⟩
      exact (Finset.mem_filter.mp hw_anc).1
    have hn_node : n ∈ G.nodes := Graph.DAG.target_mem_nodes_of_reachable hwn hw_node
    apply Finset.mem_biUnion.mpr
    use target
    constructor
    · exact Finset.mem_union_left Z htarget
    · exact Finset.mem_filter.mpr ⟨hn_node, hnt⟩
  · intro hnZ
    have h_in_cone : n ∈ {w} ∪ Graph.descendants G w := by
      by_cases h_eq : n = w
      · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr h_eq)
      · have hw_node : w ∈ G.nodes := by
          rcases Finset.mem_biUnion.mp hw with ⟨s, hs, hw_anc⟩
          exact (Finset.mem_filter.mp hw_anc).1
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr
            ⟨Graph.DAG.target_mem_nodes_of_reachable hwn hw_node, h_eq, hwn⟩)
    exact Finset.disjoint_left.mp hZ h_in_cone hnZ

end

end CausalQIF.DSeparation
