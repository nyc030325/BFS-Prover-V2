import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_113
  (x : ℝ) :
  x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by

  nlinarith [_root_.sq_nonneg (x - 7 : ℝ)]