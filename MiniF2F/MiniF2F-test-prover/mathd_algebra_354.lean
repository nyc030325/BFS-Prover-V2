import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_354
  (a d : ℝ)
  (h₀ : a + 6 * d = 30)
  (h₁ : a + 10 * d = 60) :
  a + 20 * d = 135 := by

  next => linarith [h₀, h₁]