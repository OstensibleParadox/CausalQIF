import CausalQIF.DSeparation.TraceSynthesis.MinimalWitness
import CausalQIF.DSeparation.TraceSynthesis.Split
import CausalQIF.DSeparation.TraceSynthesis.Graph

open Finset

namespace CausalQIF.DSeparation

noncomputable section

/-! # Reverse Synthesis Assembly

Final assembly layer for the reverse direction.
-/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Core structural lemma: any route with bad colliders can be strictly improved. -/
theorem route_improves_of_bad {G : Graph.DAG V} {X Y Z : Finset V}
    (w : StaticRouteWitness G X Y Z) (hbad : routeBadCount w ≠ 0) :
    ∃ w' : StaticRouteWitness G X Y Z, routeBadCount w' < routeBadCount w := by
  obtain ⟨split, hroute_eq⟩ := exists_split w.route hbad
  rcases ancestor_escape split.hchildA split.hbad with
    ⟨xNew, hxNew, hreachX⟩ | ⟨yNew, hyNew, hreachY⟩
  · have hchild : split.child ∈ G.dSeparationGraphNodes X Y Z :=
      bad_child_survives split.hchildA split.hbad
    have hnodes : ∀ n, Graph.reachable G split.child n → Graph.reachable G n xNew →
        n ∈ G.dSeparationGraphNodes X Y Z :=
      escape_path_survives split.hchildA split.hbad (Finset.mem_union.mpr (Or.inl hxNew))
    use {
      x := xNew, hx := hxNew,
      y := w.y, hy := w.hy,
      route := (StaticRoute.ofBackwardReachable hreachX hnodes).append
        (StaticRoute.cons (StaticStep.directBackward split.hbw hchild split.hb) split.suf)
    }
    dsimp [routeBadCount, StaticRouteWitness.badCount]
    have hlt :=
      countBadColliders_backwardEscape_append_suffix_lt hreachX hnodes
        split.hbw split.hb split.suf hchild
    have hbound := split.hcount
    rw [← hroute_eq]
    omega
  · have hchild : split.child ∈ G.dSeparationGraphNodes X Y Z :=
      bad_child_survives split.hchildA split.hbad
    have hnodes : ∀ n, Graph.reachable G split.child n → Graph.reachable G n yNew →
        n ∈ G.dSeparationGraphNodes X Y Z :=
      escape_path_survives split.hchildA split.hbad (Finset.mem_union.mpr (Or.inr hyNew))
    use {
      x := w.x, hx := w.hx,
      y := yNew, hy := hyNew,
      route := split.pre.append
        (StaticRoute.cons (StaticStep.directForward split.huw split.ha hchild)
          (StaticRoute.ofForwardReachable hreachY hnodes))
    }
    dsimp [routeBadCount, StaticRouteWitness.badCount]
    have hlt :=
      countBadColliders_prefix_append_forwardEscape_lt split.pre split.hprefixZero
        split.huw split.ha hreachY hnodes hchild
    have hbound := split.hcount
    rw [← hroute_eq]
    omega

/-- From moral graph reachability failure to an active trace witness. -/
theorem activeWitness_of_not_dSeparated {G : Graph.DAG V} {X Y Z : Finset V}
    (hnot : ¬ G.dSeparated X Y Z) :
    ActiveWitness G X Y Z := by
  unfold Graph.DAG.dSeparated at hnot
  push Not at hnot
  rcases hnot with ⟨x, hx, y, hy, hreach⟩
  have ⟨route⟩ := nonemptyStaticRoute_of_dSeparationGraph_reachable hreach
  have hwit : ∃ w : StaticRouteWitness G X Y Z, True :=
    ⟨⟨x, hx, y, hy, route⟩, trivial⟩
  rcases normalized_route_exists_of_improves hwit route_improves_of_bad with
    ⟨wmin, hzero⟩
  rcases activeRoute_of_countBadColliders_zero hzero with
    ⟨⟨finalDir, activeRoute⟩⟩
  exact ⟨wmin.x, wmin.hx, wmin.y, wmin.hy, finalDir, ⟨activeRoute⟩⟩

end

end CausalQIF.DSeparation
