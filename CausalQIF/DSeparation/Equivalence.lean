import CausalQIF.DSeparation.Path.Trail
import CausalQIF.DSeparation.MAGWalk

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

end

end CausalQIF.DSeparation
