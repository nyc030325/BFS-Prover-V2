import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2009_p6
  (m n p q : ℝ)
  (h₀ : p = 2 ^ m)
  (h₁ : q = 3 ^ n) :
  p^(2 * n) * (q^m) = 12^(m * n) := by

  field_simp [h₀, h₁, Real.rpow_def_of_pos, Real.rpow_def_of_pos] <;> ring
  rw [← exp_add ] <;> simp [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num,Real.log_mul] <;> ring