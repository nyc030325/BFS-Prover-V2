import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_270
  (f : ℝ → ℝ)
  (h₀ : ∀ x, x ≠ -2 -> f x = 1 / (x + 2)) :
  f (f 1) = 3/7 := by

  all_goals norm_num [h₀, ← inv_inj]