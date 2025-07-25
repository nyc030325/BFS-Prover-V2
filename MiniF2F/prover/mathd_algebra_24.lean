import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_24
  (x : ℝ)
  (h₀ : x / 50 = 40) :
  x = 2000 := by

  rw  [div_eq_iff (by norm_num)] at h₀ <;> linarith