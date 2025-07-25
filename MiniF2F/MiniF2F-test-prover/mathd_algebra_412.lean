import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_412
  (x y : ℝ)
  (h₀ : x + y = 25)
  (h₁ : x - y = 11) :
  x = 18 := by

  linarith <;>
  apply symm <;>
  linarith