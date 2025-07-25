import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2021_p9 :
  (Real.log 80 / Real.log 2) / (Real.log 2 / Real.log 40) - (Real.log 160 / Real.log 2) / (Real.log 2 / Real.log 20) = 2 := by

  field_simp [show (80 : ℝ) = 2 ^ 4 * 5 by norm_cast, show (160 : ℝ) = 2 ^ 5 * 5 by norm_cast,
    show (40 : ℝ) = 2 ^ 3 * 5 by norm_cast, show (20 : ℝ) = 2 ^ 2 * 5 by norm_cast] <;>
  simp [Real.log_mul] <;> ring