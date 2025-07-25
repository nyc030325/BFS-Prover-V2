import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_143
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 1)
  (h₁ : ∀ x, g x = x^2 + 3) :
  f (g 2) = 8 := by

  norm_num[Function.funext_iff,h₀,h₁]