import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2020_p13 :
  Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) = Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) := by

  iterate 1 field_simp [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul]
  rw [Real.sqrt_eq_iff_mul_self_eq] <;>
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 3)]