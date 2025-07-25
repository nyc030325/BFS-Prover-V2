import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_171
  (f : ℝ → ℝ)
  (h₀ : ∀x, f x = 5 * x + 4) :
  f 1 = 9 := by

  linarith [h₀ 2, h₀ 1, h₀ 0]