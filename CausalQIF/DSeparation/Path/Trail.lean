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

/-- Direction-only blocking agrees with the usual triple-blocking predicate
when the two directed edge orientations match the adjacent trail steps. -/
lemma directionalTripleBlocked_iff_tripleBlocked {G : Graph.DAG V} {Z : Finset V}
    {a b c : V} {arrival departure : TrailDir}
    (hab : TrailDir.edgeIntoCurrent G a b arrival)
    (hbc : TrailDir.edgeIntoCurrent G b c departure) :
    directionalTripleBlocked G Z b arrival departure ↔ tripleBlocked G Z a b c := by
  cases arrival <;> cases departure
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_cb : ¬ G.hasEdge c b := G.not_hasEdge_reverse_of_hasEdge hbc
    have hnot : ¬ tripleCollider G a b c := fun hcoll => hnot_cb hcoll.2
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hnot]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hcoll : tripleCollider G a b c := ⟨hab, hbc⟩
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hcoll]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_ab : ¬ G.hasEdge a b := G.not_hasEdge_reverse_of_hasEdge hab
    have hnot : ¬ tripleCollider G a b c := fun hcoll => hnot_ab hcoll.1
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hnot]
  · simp [TrailDir.edgeIntoCurrent] at hab hbc
    have hnot_ab : ¬ G.hasEdge a b := G.not_hasEdge_reverse_of_hasEdge hab
    have hnot : ¬ tripleCollider G a b c := fun hcoll => hnot_ab hcoll.1
    simp [directionalTripleBlocked, TrailDir.colliderAtCurrent, tripleBlocked, hnot]

/--
Bayes-ball step relation over `(node, arrival-direction)` states.  A step is
available when the edge to the next node has the recorded orientation and the
local direction-only triple at the current node is not blocked by `Z`.
-/
inductive BayesBallStep (G : Graph.DAG V) (Z : Finset V) :
    V × TrailDir → V × TrailDir → Prop where
  | step {v w : V} {arrival departure : TrailDir}
      (hEdge : TrailDir.edgeIntoCurrent G v w departure)
      (hopen : ¬ directionalTripleBlocked G Z v arrival departure) :
      BayesBallStep G Z (v, arrival) (w, departure)

/-- Reachability in the Bayes-ball state graph. -/
def BayesBallReachable (G : Graph.DAG V) (Z : Finset V)
    (s t : V × TrailDir) : Prop :=
  Relation.ReflTransGen (BayesBallStep G Z) s t

/-- Explicit Bayes-ball paths, used when proofs need a two-step scan window. -/
inductive BayesBallPath (G : Graph.DAG V) (Z : Finset V) :
    V × TrailDir → V × TrailDir → Type where
  | nil (s : V × TrailDir) : BayesBallPath G Z s s
  | cons {s t u : V × TrailDir}
      (step : BayesBallStep G Z s t)
      (rest : BayesBallPath G Z t u) :
      BayesBallPath G Z s u

namespace BayesBallPath

/-- Number of Bayes-ball steps in an explicit path. -/
def length {G : Graph.DAG V} {Z : Finset V} :
    {s t : V × TrailDir} → BayesBallPath G Z s t → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ rest => rest.length + 1

/-- Forget an explicit Bayes-ball path to reflexive-transitive reachability. -/
def toReachable {G : Graph.DAG V} {Z : Finset V} :
    {s t : V × TrailDir} → BayesBallPath G Z s t → BayesBallReachable G Z s t
  | _, _, nil _ => Relation.ReflTransGen.refl
  | _, _, cons step rest => (Relation.ReflTransGen.single step).trans rest.toReachable

/-- Append a final Bayes-ball step to an explicit path. -/
def snoc {G : Graph.DAG V} {Z : Finset V} {s t u : V × TrailDir}
    (p : BayesBallPath G Z s t) (step : BayesBallStep G Z t u) :
    BayesBallPath G Z s u :=
  match p with
  | nil _ => cons step (nil u)
  | cons head rest => cons head (rest.snoc step)

/--
States whose node-membership proof is required by the compressed path scanner.
For a collider window `(a, _) → (b, into) → (c, outOf)`, the scanner jumps
directly from `a` to `c`, so `b` is deliberately not required here.
-/
inductive RequiredState {G : Graph.DAG V} {Z : Finset V} :
    {s t : V × TrailDir} → BayesBallPath G Z s t → V × TrailDir → Prop where
  | one {s mid : V × TrailDir} (step : BayesBallStep G Z s mid) :
      RequiredState (BayesBallPath.cons step (BayesBallPath.nil mid)) mid
  | colliderTarget {s mid next finish : V × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      (hcoll : mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) next
  | colliderRest {s mid next finish : V × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      {q : V × TrailDir}
      (hcoll : mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf)
      (hreq : RequiredState rest q) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) q
  | noncolliderTarget {s mid next finish : V × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      (hnot : ¬ (mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf)) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) mid
  | noncolliderRest {s mid next finish : V × TrailDir}
      {step₁ : BayesBallStep G Z s mid}
      {step₂ : BayesBallStep G Z mid next}
      {rest : BayesBallPath G Z next finish}
      {q : V × TrailDir}
      (hnot : ¬ (mid.2 = TrailDir.into ∧ next.2 = TrailDir.outOf))
      (hreq : RequiredState (BayesBallPath.cons step₂ rest) q) :
      RequiredState (BayesBallPath.cons step₁ (BayesBallPath.cons step₂ rest)) q

/-- A first target reached with `outOf` arrival is never a collider target. -/
lemma required_first_target_of_outOf {G : Graph.DAG V} {Z : Finset V}
    {s mid finish : V × TrailDir}
    (step : BayesBallStep G Z s mid)
    (rest : BayesBallPath G Z mid finish)
    (hmid : mid.2 = TrailDir.outOf) :
    RequiredState (BayesBallPath.cons step rest) mid := by
  cases rest with
  | nil _ =>
      exact RequiredState.one step
  | cons step₂ rest₂ =>
      exact RequiredState.noncolliderTarget (by
        intro hcoll
        rw [hmid] at hcoll
        cases hcoll.1)

/-- Required states of a suffix remain required after an `outOf` first target. -/
lemma required_rest_of_outOf {G : Graph.DAG V} {Z : Finset V}
    {s mid finish : V × TrailDir}
    (step : BayesBallStep G Z s mid)
    (rest : BayesBallPath G Z mid finish)
    (hmid : mid.2 = TrailDir.outOf)
    {q : V × TrailDir}
    (hreq : RequiredState rest q) :
    RequiredState (BayesBallPath.cons step rest) q := by
  cases rest with
  | nil _ =>
      cases hreq
  | cons step₂ rest₂ =>
      exact RequiredState.noncolliderRest (by
        intro hcoll
        rw [hmid] at hcoll
        cases hcoll.1) hreq

end BayesBallPath

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

lemma not_trailBlocked_tail_of_not_trailBlocked_cons {G : Graph.DAG V} {Z : Finset V}
    {xs : List V} {x : V}
    (h : ¬ trailBlocked G Z (x :: xs)) :
    ¬ trailBlocked G Z xs := by
  intro htail
  rcases htail with ⟨a, b, c, htriple, hblocked⟩
  exact h ⟨a, b, c, hasTriple.cons htriple, hblocked⟩

lemma trailBlocked_of_head_tripleBlocked {G : Graph.DAG V} {Z : Finset V}
    {a b c : V} {xs : List V}
    (h : tripleBlocked G Z a b c) :
    trailBlocked G Z (a :: b :: c :: xs) :=
  ⟨a, b, c, ⟨[], xs, rfl⟩, h⟩

lemma not_tripleBlocked_head_of_not_trailBlocked {G : Graph.DAG V} {Z : Finset V}
    {a b c : V} {xs : List V}
    (h : ¬ trailBlocked G Z (a :: b :: c :: xs)) :
    ¬ tripleBlocked G Z a b c := by
  intro htriple
  exact h (trailBlocked_of_head_tripleBlocked htriple)

lemma trailBlocked_of_head_tripleBlocked_trail {G : Graph.DAG V} {Z : Finset V}
    {a b c v : V} {t : Trail G c v}
    (h : tripleBlocked G Z a b c) :
    trailBlocked G Z (a :: b :: t.toList) :=
  ⟨a, b, c, hasTriple.head_of_trail t, h⟩

lemma not_tripleBlocked_head_of_not_trailBlocked_trail {G : Graph.DAG V} {Z : Finset V}
    {a b c v : V} {t : Trail G c v}
    (h : ¬ trailBlocked G Z (a :: b :: t.toList)) :
    ¬ tripleBlocked G Z a b c := by
  intro htriple
  exact h (trailBlocked_of_head_tripleBlocked_trail htriple)

end

end CausalQIF.DSeparation
