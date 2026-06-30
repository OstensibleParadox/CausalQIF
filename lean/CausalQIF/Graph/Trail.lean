import CausalQIF.DSeparation.Trail
import CausalQIF.DSeparation.BayesBall

/-!
# Trail Layer

Canonical graph-trail primitives re-exported from `DSeparation/Trail` and
`DSeparation/BayesBall`.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

namespace CausalQIF

namespace Graph

export CausalQIF (
  Consecutive
  HasTriple
  Trail
  Trail.toList
  Trail.nodes
  Trail.mem_nodes
  Trail.target_mem_graph_nodes_of_source_mem
  TripleCollider
  TripleBlocked
  DirectionalTripleBlocked
  TrailDir
  TrailDir.edgeIntoCurrent
  TrailDir.colliderAtCurrent
  directionalTripleBlocked_iff_tripleBlocked
  trailBlocked_of_head_tripleBlocked
  trailBlocked_of_head_tripleBlocked_trail
  trailBlocked_of_tail_of_not_trailBlocked
  not_trailBlocked_tail_of_not_trailBlocked_cons
  not_tripleBlocked_head_of_not_trailBlocked
  not_tripleBlocked_head_of_not_trailBlocked_trail
  BayesBallStep
  BayesBallPath
  BayesBallReachable
  bayesBallReachable_of_active_trail
  bayesBallReachable_of_active_trail_from_prev
  bayesBallReachable_of_active_trail_outOf
  TrailBlocked
  TrailBlocked.cons
  BayesBallReachable.toReachable
  BayesBallStep.of_active_triple
)

end Graph

end CausalQIF
