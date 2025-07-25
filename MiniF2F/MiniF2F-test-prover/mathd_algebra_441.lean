import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_441
  (x : ℝ)
  (h₀ : x ≠ 0) :
  12 / (x * x) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := by

  by_cases hi : x = 0 <;> field_simp at * <;> ring