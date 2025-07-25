import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_400
  (x : ℝ)
  (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) :
  x = 50 := by

  rw  [eq_comm] <;> norm_num at * <;>linarith