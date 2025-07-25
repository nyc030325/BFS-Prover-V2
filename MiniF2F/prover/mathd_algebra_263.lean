import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_263
  (y : ℝ)
  (h₀ : 0 ≤ 19 + 3 * y)
  (h₁ : Real.sqrt (19 + 3 * y) = 7) :
  y = 10 := by

  nlinarith[Real.sq_sqrt (show 0 ≤ (19 + 3 * y) by linarith)]