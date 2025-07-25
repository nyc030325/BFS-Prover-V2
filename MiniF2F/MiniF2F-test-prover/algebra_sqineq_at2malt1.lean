import Mathlib
open BigOperators Real Nat Topology

theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by

  linarith [_root_.sq_nonneg (a - 1), _root_.sq_nonneg (-a - 1)] <;> linarith