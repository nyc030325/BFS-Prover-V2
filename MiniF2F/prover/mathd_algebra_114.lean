import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_114
  (a : ℝ)
  (h₀ : a = 8) :
  (16 * (a^2) ^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) = 4 := by

  norm_num [@Real.rpow_def_of_nonneg, h₀]
  field_simp [show (64 : ℝ) = 4 ^ 3 by norm_cast] <;> norm_num [Real.exp_log] <;> rw [Real.rpow_def_of_pos] <;>
    norm_num
  field_simp [show (64 : ℝ) = (4 : ℝ) ^ 3 by norm_cast, Real.exp_log]