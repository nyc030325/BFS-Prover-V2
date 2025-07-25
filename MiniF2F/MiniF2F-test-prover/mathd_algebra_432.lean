import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_432
  (x : ℝ) :
  (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by

  nlinarith <;> ring