import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_275
  (x : ℝ)
  (h : ((11:ℝ)^(1 / 4))^(3 * x - 3) = 1 / 5) :
  ((11:ℝ)^(1 / 4))^(6 * x + 2) = 121 / 25 := by

  norm_num [Real.rpow_def_of_pos] at h ⊢