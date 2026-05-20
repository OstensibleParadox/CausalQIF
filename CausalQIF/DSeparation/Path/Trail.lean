import CausalQIF.DSeparation.Path.Trail.Basic
import CausalQIF.DSeparation.Path.Trail.Triple
import CausalQIF.DSeparation.Path.Trail.BayesBall
import CausalQIF.DSeparation.Path.Trail.Blocking

/-!
# Trail Module Wrapper

Re-exports the four submodules of trail-based d-separation:
* `Trail.Basic` — the `Trail` inductive and structural helpers.
* `Trail.Triple` — triple/collider/blocking predicates and `TrailDir`.
* `Trail.BayesBall` — Bayes-ball walker state graph, paths, required-state induction.
* `Trail.Blocking` — `hasTriple`, `trailBlocked`, `Trail.isBlocked`, `dSeparates`.
-/
