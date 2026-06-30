/-!
# D-Separation Layer

Canonical DAG and d-separation re-export layer for graph reasoning.

Authors: (C) 2026 CausalQIF artifact contributors.
-/

import CausalQIF.DSeparation.DAG

namespace CausalQIF

namespace Graph

export CausalQIF (
  Reachable
  DAG
  DAG.HasEdge
  DAG.ofRank
  DAG.RespectsTopologicalRank
  DAG.ancestors
  DAG.ancestralSubgraph
  DAG.ancestralSubgraphNodes
  DAG.deleteLeaf
  DSeparationQuery
  DSeparationQuery_iff_DisjointSets
  DisjointSets
  dSeparates
  Trail
  Trail.toList
  Trail.nodes
  Trail.mem_nodes
  Trail.target_mem_graph_nodes_of_source_mem
  TripleCollider
  TripleBlocked
)

end Graph

end CausalQIF
