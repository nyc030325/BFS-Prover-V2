import Mathlib
open BigOperators Real Nat Topology

theorem algebra_sqineq_unitcircatbpamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + (a - b) ≤ 1 := by

  nlinarith [mul_self_nonneg (a - b),
             mul_self_nonneg (a + b),
             sq_nonneg (a - 1)]