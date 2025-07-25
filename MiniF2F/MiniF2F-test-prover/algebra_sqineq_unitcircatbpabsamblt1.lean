import Mathlib
open BigOperators Real Nat Topology

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by

  cases le_total (a - b) 0 <;>
  norm_num <;>
  nlinarith [sq_abs (a - b)] <;> nlinarith