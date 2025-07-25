import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_388
  (x y z : ℝ)
  (h₀ : 3 * x + 4 * y - 12 * z = 10)
  (h₁ : -2 * x - 3 * y + 9 * z = -4) :
  x = 14 := by

  nlinarith
          <;> rw [eq_comm]
          <;> try linarith