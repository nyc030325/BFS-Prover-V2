import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_302 :
  (Complex.I / 2)^2 = -(1 / 4) := by

  all_goals field_simp [pow_two, div_mul_eq_mul_div]; ring