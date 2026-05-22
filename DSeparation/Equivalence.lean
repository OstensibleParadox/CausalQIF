import CausalQIF.DSeparation.Path.Trail
import CausalQIF.DSeparation.MAGWalk
import CausalQIF.DSeparation.TraceSynthesis.Assembly

open Finset

namespace CausalQIF.DSeparation

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# D-Separation Equivalence Interfaces

This module keeps the main library's verified d-separation surface inside the
`CausalQIF` namespace.  The exported equivalence here is between the moralized
ancestral graph predicate `Graph.DAG.dSeparated` and the compressed `MAGWalk`
reachability certificate.  The trail-blocking predicate `dSeparates` remains the
semantic hypothesis consumed by the probabilistic factorization layer.
-/

theorem dSeparated_iff_no_magWalk
    {G : Graph.DAG V} {X Y Z : Finset V} :
    G.dSeparated X Y Z ↔
      ∀ x, x ∈ X → ∀ y, y ∈ Y → ¬ MAGWalk G X Y Z x y := by
  constructor
  · intro hsep x hx y hy hwalk
    exact hsep x hx y hy ((magWalk_iff_dSeparationGraph_reachable).mp hwalk)
  · intro hwalk x hx y hy hreach
    exact hwalk x hx y hy ((magWalk_iff_dSeparationGraph_reachable).mpr hreach)

theorem no_magWalk_of_dSeparated
    {G : Graph.DAG V} {X Y Z : Finset V}
    (hsep : G.dSeparated X Y Z) :
    ∀ x, x ∈ X → ∀ y, y ∈ Y → ¬ MAGWalk G X Y Z x y :=
  dSeparated_iff_no_magWalk.mp hsep

theorem dSeparated_of_no_magWalk
    {G : Graph.DAG V} {X Y Z : Finset V}
    (hwalk : ∀ x, x ∈ X → ∀ y, y ∈ Y → ¬ MAGWalk G X Y Z x y) :
    G.dSeparated X Y Z :=
  dSeparated_iff_no_magWalk.mpr hwalk

theorem dSeparates_iff_all_trails_blocked
    {G : Graph.DAG V} {X Y Z : Finset V} :
    dSeparates G X Y Z ↔
      ∀ x, x ∈ X → ∀ y, y ∈ Y → ∀ t : Trail G x y, t.isBlocked Z :=
  Iff.rfl

theorem dSeparationGraph_reachable_of_active_trail_disjoint
    {G : Graph.DAG V} {X Y Z : Finset V} {x y : V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hxX : x ∈ X) (hyY : y ∈ Y)
    (t : Trail G x y) (h_active : ¬ t.isBlocked Z) :
    (G.dSeparationGraph X Y Z).Reachable x y := by
  have hxZ : x ∉ Z := Graph.DAG.not_mem_right_of_disjoint_left hXZ hxX
  have hyZ : y ∉ Z := Graph.DAG.not_mem_right_of_disjoint_left hYZ hyY
  cases t with
  | nil x =>
      exact SimpleGraph.Reachable.refl x
  | forward h tail =>
      rename_i w
      have hxG : x ∈ G.nodes := (G.edges_subset h).1
      have hyG : y ∈ G.nodes :=
        Trail.target_mem_graph_nodes_of_source_mem
          (Trail.forward (G := G) (u := x) (w := w) (v := y) h tail) hxG
      have hxD : x ∈ G.dSeparationGraphNodes X Y Z :=
        Graph.DAG.mem_dSeparationGraphNodes_of_mem_left hxX hxG hxZ
      have hyD : y ∈ G.dSeparationGraphNodes X Y Z :=
        Graph.DAG.mem_dSeparationGraphNodes_of_mem_right hyY hyG hyZ
      have hxA : x ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hxD
      rcases bayesBallPathCert_of_active_trail_outOf
          (G := G) (X := X) (Y := Y) (Z := Z)
          (u := x) (v := y)
          (Trail.forward (G := G) (u := x) (w := w) (v := y) h tail)
          h_active hxZ hxA hyD with
        ⟨final_dir, ⟨p, hreq⟩⟩
      exact MAGWalk.to_dSeparationGraph_reachable
        (BayesBallPath.compress
          (G := G) (X := X) (Y := Y) (Z := Z)
          (s := (x, TrailDir.outOf)) (t := (y, final_dir))
          p hxD hyD hreq)
  | backward h tail =>
      rename_i w
      have hxG : x ∈ G.nodes := (G.edges_subset h).2
      have hyG : y ∈ G.nodes :=
        Trail.target_mem_graph_nodes_of_source_mem
          (Trail.backward (G := G) (u := x) (w := w) (v := y) h tail) hxG
      have hxD : x ∈ G.dSeparationGraphNodes X Y Z :=
        Graph.DAG.mem_dSeparationGraphNodes_of_mem_left hxX hxG hxZ
      have hyD : y ∈ G.dSeparationGraphNodes X Y Z :=
        Graph.DAG.mem_dSeparationGraphNodes_of_mem_right hyY hyG hyZ
      have hxA : x ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) :=
        mem_ancestralSubgraphNodes_of_mem_dSeparationGraphNodes hxD
      rcases bayesBallPathCert_of_active_trail_outOf
          (G := G) (X := X) (Y := Y) (Z := Z)
          (u := x) (v := y)
          (Trail.backward (G := G) (u := x) (w := w) (v := y) h tail)
          h_active hxZ hxA hyD with
        ⟨final_dir, ⟨p, hreq⟩⟩
      exact MAGWalk.to_dSeparationGraph_reachable
        (BayesBallPath.compress
          (G := G) (X := X) (Y := Y) (Z := Z)
          (s := (x, TrailDir.outOf)) (t := (y, final_dir))
          p hxD hyD hreq)

theorem dsep_complete_of_endpoint_disjoint
    {G : Graph.DAG V} {X Y Z : Finset V}
    (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    G.dSeparated X Y Z → dSeparates G X Y Z := by
  intro hdsep x hxX y hyY t
  by_contra h_active
  exact hdsep x hxX y hyY
    (dSeparationGraph_reachable_of_active_trail_disjoint
      (G := G) (X := X) (Y := Y) (Z := Z)
      hXZ hYZ hxX hyY t h_active)

theorem dsep_complete_of_query
    {G : Graph.DAG V} {X Y Z : Finset V}
    (hquery : disjointSets X Y Z) :
    G.dSeparated X Y Z → dSeparates G X Y Z :=
  dsep_complete_of_endpoint_disjoint hquery.2.1 hquery.2.2

/-- If `X`, `Y`, and `Z` are pairwise disjoint, graph separation implies that
every trail from `X` to `Y` is blocked by `Z`. -/
theorem dSeparated_of_dSeparated_disjoint
    {G : Graph.DAG V} {X Y Z : Finset V}
    (hXYZ : disjointSets X Y Z)
    (hsep : G.dSeparated X Y Z) : dSeparates G X Y Z := by
  exact dsep_complete_of_endpoint_disjoint hXYZ.2.1 hXYZ.2.2 hsep

/-- If an active witness exists, then `X` and `Y` are not d-separated by `Z`. -/
theorem activeWitness_implies_not_dSeparates {G : Graph.DAG V} {X Y Z : Finset V}
    (w : ActiveWitness G X Y Z) : ¬ dSeparates G X Y Z := by
  rcases w with ⟨x, hx, y, hy, d, ⟨route⟩⟩
  rcases ActiveRoute.to_activeTrail route with ⟨tr, h_active⟩
  intro hsep
  exact h_active (hsep x hx y hy tr)

/-- Full equivalence between moralized-ancestral graph separation and
trail-blocking d-separation under the standard pairwise-disjoint query domain. -/
theorem dSeparated_iff_dSeparates
    {G : Graph.DAG V} {X Y Z : Finset V} (hXYZ : disjointSets X Y Z) :
    G.dSeparated X Y Z ↔ dSeparates G X Y Z := by
  constructor
  · exact dSeparated_of_dSeparated_disjoint hXYZ
  · intro hsep
    by_contra hnot
    have hwit := activeWitness_of_not_dSeparated hnot
    exact (activeWitness_implies_not_dSeparates hwit) hsep

end

end CausalQIF.DSeparation
