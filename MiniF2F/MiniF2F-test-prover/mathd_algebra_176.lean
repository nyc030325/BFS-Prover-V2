import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_176
  (x : ℝ) :
  (x + 1)^2 * x = x^3 + 2 * x^2 + x := by

  cases x <;> ring