import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_419
  (a b : ℝ)
  (h₀ : a = -1)
  (h₁ : b = 5) :
  -a - b^2 + 3 * (a * b) = -39 := by

  nlinarith [pow_two_nonneg (a - 6), pow_two_nonneg b]