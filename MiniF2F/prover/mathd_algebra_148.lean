import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_148
  (c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = c * x^3 - 9 * x + 3)
  (h₁ : f 2 = 9) :
  c = 3 := by

  calc c = 3 := by nlinarith [h₀ 2, h₀ 1, h₀ 0, h₀ (-1), h₀ (-2) ]