import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_246
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^4 - b * x^2 + x + 5)
  (h₂ : f (-3) = 2) :
  f 3 = 8 := by

  simp_all [_root_.pow_succ] <;> linarith