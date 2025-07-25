import Mathlib
open BigOperators Real Nat Topology

theorem aime_1983_p2
  (x p : ℝ)
  (f : ℝ → ℝ)
  (h₀ : 0 < p ∧ p < 15)
  (h₁ : p ≤ x ∧ x ≤ 15)
  (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
  15 ≤ f x := by

  cases abs_cases (x - p) <;> cases abs_cases (x - 15) <;> cases abs_cases (x - p - 15) <;>
    linarith [abs_nonneg (p - 15), abs_nonneg (15 - x)]