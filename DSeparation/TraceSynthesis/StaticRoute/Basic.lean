import CausalQIF.DSeparation.MAGWalk

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Static Route IR

Type-valued evidence for walks in the d-separation graph.  This layer keeps the
directed-edge and moral-jump witnesses that are hidden by graph reachability.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A single step in the d-separation graph, as explicit evidence. -/
inductive StaticStep (G : Graph.DAG V) (X Y Z : Finset V) : V → V → Type where
  | directForward {u v : V}
      (hEdge : G.hasEdge u v)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
      StaticStep G X Y Z u v
  | directBackward {u v : V}
      (hEdge : G.hasEdge v u)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z) :
      StaticStep G X Y Z u v
  | moralJump {u v w : V}
      (huw : G.hasEdge u w)
      (hvw : G.hasEdge v w)
      (hne : u ≠ v)
      (hu : u ∈ G.dSeparationGraphNodes X Y Z)
      (hv : v ∈ G.dSeparationGraphNodes X Y Z)
      (hw : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z)) :
      StaticStep G X Y Z u v

/-- A route is a sequence of static steps. -/
inductive StaticRoute (G : Graph.DAG V) (X Y Z : Finset V) : V → V → Type where
  | nil (u : V) : StaticRoute G X Y Z u u
  | cons {u v w : V}
      (step : StaticStep G X Y Z u v)
      (rest : StaticRoute G X Y Z v w) :
      StaticRoute G X Y Z u w

namespace StaticStep

/-- Every static step gives a MAG walk step. -/
def toMAGWalk {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (step : StaticStep G X Y Z u v) : MAGWalk G X Y Z u v :=
  match step with
  | directForward hEdge hu hv => MAGWalk.single (Or.inl hEdge) hu hv
  | directBackward hEdge hu hv => MAGWalk.single (Or.inr hEdge) hu hv
  | moralJump huw hvw hne hu hv hw => MAGWalk.jump huw hvw hne hu hv hw

/-- Convert a single adjacency in the d-separation graph to a static step. -/
noncomputable def ofDSeparationGraphAdj {G : Graph.DAG V} {X Y Z : Finset V}
    {u v : V} (h : (G.dSeparationGraph X Y Z).Adj u v) :
    StaticStep G X Y Z u v :=
  Classical.choice (show Nonempty (StaticStep G X Y Z u v) from by
    rcases h with ⟨hu, hv, hmoral⟩
    dsimp [Graph.DAG.moralGraph] at hmoral
    rcases hmoral with ⟨_huA, _hvA, _hne, hdir | hrev | hcop⟩
    · have huv : G.hasEdge u v := by
        simp only [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge, Finset.mem_filter] at hdir ⊢
        exact hdir.1
      exact ⟨StaticStep.directForward huv hu hv⟩
    · have hvu : G.hasEdge v u := by
        simp only [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge, Finset.mem_filter] at hrev ⊢
        exact hrev.1
      exact ⟨StaticStep.directBackward hvu hu hv⟩
    · rcases hcop with ⟨w, huw', hvw', hne_uv⟩
      have huw : G.hasEdge u w := by
        simp only [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge, Finset.mem_filter] at huw' ⊢
        exact huw'.1
      have hvw : G.hasEdge v w := by
        simp only [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge, Finset.mem_filter] at hvw' ⊢
        exact hvw'.1
      have hwA : w ∈ G.ancestralSubgraphNodes (X ∪ Y ∪ Z) := by
        simp only [Graph.DAG.ancestralSubgraph, Graph.DAG.hasEdge, Finset.mem_filter] at huw' ⊢
        exact huw'.2.2
      exact ⟨StaticStep.moralJump huw hvw hne_uv hu hv hwA⟩)

/-- The arrival direction at the destination of a static step. -/
def nextArrival {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (step : StaticStep G X Y Z u v) : TrailDir :=
  match step with
  | StaticStep.directForward .. => TrailDir.into
  | StaticStep.directBackward .. => TrailDir.outOf
  | StaticStep.moralJump .. => TrailDir.outOf

end StaticStep

namespace StaticRoute

/-- Every static route gives a MAG walk. -/
def toMAGWalk {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (route : StaticRoute G X Y Z u v) : MAGWalk G X Y Z u v :=
  match route with
  | nil u => MAGWalk.refl u
  | cons step rest => MAGWalk.trans step.toMAGWalk rest.toMAGWalk

/-- Append two static routes. -/
def append {G : Graph.DAG V} {X Y Z : Finset V} {u v w : V}
    (p : StaticRoute G X Y Z u v) (q : StaticRoute G X Y Z v w) :
    StaticRoute G X Y Z u w :=
  match p with
  | nil _ => q
  | cons step rest => cons step (rest.append q)

lemma append_nil {G : Graph.DAG V} {X Y Z : Finset V} {x y : V}
    (route : StaticRoute G X Y Z x y) :
    route.append (StaticRoute.nil y) = route := by
  induction route with
  | nil _ => rfl
  | cons _ _ ih => dsimp [append]; rw [ih]

lemma append_assoc {G : Graph.DAG V} {X Y Z : Finset V} {x y z w : V}
    (p : StaticRoute G X Y Z x y) (q : StaticRoute G X Y Z y z)
    (r : StaticRoute G X Y Z z w) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil _ => rfl
  | cons step rest ih => dsimp [append]; rw [ih]

/-- Length of a static route, measured in static steps. -/
def length {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (route : StaticRoute G X Y Z u v) : ℕ :=
  match route with
  | nil _ => 0
  | cons _ rest => rest.length + 1

/-- The arrival direction at the end of a static route. -/
def finalArrival {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (initialArrival : TrailDir) (route : StaticRoute G X Y Z u v) : TrailDir :=
  match route with
  | nil _ => initialArrival
  | cons step rest => rest.finalArrival step.nextArrival

/-- From a `SimpleGraph.Walk` in the d-separation graph, build a static route. -/
noncomputable def ofDSeparationGraphWalk {G : Graph.DAG V} {X Y Z : Finset V}
    {u v : V} (p : SimpleGraph.Walk (G.dSeparationGraph X Y Z) u v) :
    StaticRoute G X Y Z u v := by
  induction p with
  | nil =>
      exact StaticRoute.nil _
  | cons hAdj _ ih =>
      exact StaticRoute.cons (StaticStep.ofDSeparationGraphAdj hAdj) ih

end StaticRoute

/-- From reachability in the d-separation graph, obtain a static route. -/
theorem nonemptyStaticRoute_of_dSeparationGraph_reachable
    {G : Graph.DAG V} {X Y Z : Finset V} {u v : V}
    (h : (G.dSeparationGraph X Y Z).Reachable u v) :
    Nonempty (StaticRoute G X Y Z u v) := by
  rcases h with ⟨p⟩
  exact ⟨StaticRoute.ofDSeparationGraphWalk p⟩

end

end CausalQIF.DSeparation
