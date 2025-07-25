import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_359
  (y : ℝ)
  (h₀ : y + 6 + y = 2 * 12) :
  y = 9 := by

  linarith <;> linarith![h₀]