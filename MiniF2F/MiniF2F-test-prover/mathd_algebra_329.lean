import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_329
  (x y : ℝ)
  (h₀ : 3 * y = x)
  (h₁ : 2 * x + 5 * y = 11) :
  x + y = 4 := by

  linarith <;> (revert h₀ h₁; intros; linarith)