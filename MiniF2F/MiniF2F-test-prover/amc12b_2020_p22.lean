import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2020_p22
  (t : ℝ) :
  ((2^t - 3 * t) * t) / (4^t) ≤ 1 / 12 := by

  have := Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) t
  field_simp [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), this]
  field_simp [show Real.log (4 : ℝ) = Real.log (2 ^ 2) by norm_num]
  field_simp [show (2 : ℝ) * Real.log 2 * t = Real.log 2 * t + Real.log 2 * t by ring_nf]
  simp [Real.exp_add, mul_add]
  rw [_root_.div_le_iff] <;> norm_num
  nlinarith [sq_nonneg (exp (Real.log 2 * t) - 6 * t), Real.add_one_le_exp (Real.log 2 * t),
      sq_nonneg t]