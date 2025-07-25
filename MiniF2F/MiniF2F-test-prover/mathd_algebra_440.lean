import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_440
  (x : ℝ)
  (h₀ : 3 / 2 / 3 = x / 10) :
  x = 5 := by

  norm_num [eq_div_iff] at *<;> linarith