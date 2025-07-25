import Mathlib
open BigOperators Real Nat Topology

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by

  aesop (add simp [sq]) <;> norm_num
  field_simp [left.le, left_1.le, left_2.le, right.le] at *
  rw [le_div_iff (by positivity)] <;>
    nlinarith [mul_pos left left_1, mul_pos left_1 left_2, mul_pos left_2 right, mul_pos right left,sq_nonneg (a*c - b^2), sq_nonneg (a*d - c^2), sq_nonneg (b*d - a*c),
    mul_nonneg left.le (sq_nonneg <| c - d), mul_nonneg left_1.le (sq_nonneg <| a - d), mul_nonneg left_2.le (sq_nonneg <| a - b), mul_nonneg right.le  (sq_nonneg <| b - c)]