import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_338
  (a b c : ℝ)
  (h₀ : 3 * a + b + c = -3)
  (h₁ : a + 3 * b + c = 9)
  (h₂ : a + b + 3 * c = 19) :
  a * b * c = -56 := by

  nlinarith [sq_nonneg c, sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (a - c)]