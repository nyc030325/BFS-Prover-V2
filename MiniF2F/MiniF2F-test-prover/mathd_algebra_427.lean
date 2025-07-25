import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_427
  (x y z : ℝ)
  (h₀ : 3 * x + y = 17)
  (h₁ : 5 * y + z = 14)
  (h₂ : 3 * x + 5 * z = 41) :
  x + y + z = 12 := by

  linarith [sq ((((z - y) - (3 : ℝ) * (x - y)) - (z - y)) - (3 : ℝ) * (x - y))]