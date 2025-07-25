import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_80
  (x : ℝ)
  (h₀ : x ≠ -1)
  (h₁ : (x - 9) / (x + 1) = 2) :
  x = -11 := by

  rcases eq_or_ne (x + 1) 0 with hix|hix <;>field_simp[*] at h₁ <;>linarith