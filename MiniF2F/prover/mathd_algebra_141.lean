import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_141
  (a b : ℝ)
  (h₁ : (a * b)=180)
  (h₂ : 2 * (a + b)=54) :
  (a^2 + b^2) = 369 := by

  repeat' nlinarith [two_mul (a + b), h₁]