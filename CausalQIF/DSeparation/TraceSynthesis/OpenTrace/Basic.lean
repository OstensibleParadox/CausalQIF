import CausalQIF.DSeparation.ActiveRoute
import CausalQIF.DSeparation.TraceSynthesis.StaticRoute

open Finset
open Classical

namespace CausalQIF.DSeparation

noncomputable section

/-! # Open Traces

The compiler target for static routes before converting to `ActiveRoute`.
Each step stores its oriented DAG traversal and the local non-blocking
obligation needed by Bayes-ball.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An expanded trace that records oriented traversals and local open junctions. -/
inductive OpenTrace (G : Graph.DAG V) (Z : Finset V) :
    V × TrailDir → V × TrailDir → Type where
  | nil (s : V × TrailDir) : OpenTrace G Z s s
  | cons {u v w : V} {arrival departure finalDir : TrailDir}
      (hEdge : TrailDir.edgeIntoCurrent G u v departure)
      (hOpen : ¬ directionalTripleBlocked G Z u arrival departure)
      (rest : OpenTrace G Z (v, departure) (w, finalDir)) :
      OpenTrace G Z (u, arrival) (w, finalDir)

namespace OpenTrace

/-- Convert an open trace to a propositional Bayes-ball path. -/
def toBayesBallPath {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (p : OpenTrace G Z s t) : BayesBallPath G Z s t :=
  match p with
  | nil s => BayesBallPath.nil s
  | cons hEdge hOpen rest =>
      BayesBallPath.cons (BayesBallStep.step hEdge hOpen) rest.toBayesBallPath

/-- Convert an open trace to the final `ActiveRoute` witness. -/
def toActiveRoute {G : Graph.DAG V} {Z : Finset V} {s t : V × TrailDir}
    (p : OpenTrace G Z s t) : ActiveRoute G Z s t :=
  ⟨p.toBayesBallPath⟩

end OpenTrace

end

end CausalQIF.DSeparation
