import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_160
  (n x : ℝ)
  (h₀ : n + x = 97)
  (h₁ : n + 5 * x = 265) :
  n + 2 * x = 139 := by

  nlinarith [_root_.mul_comm n x]