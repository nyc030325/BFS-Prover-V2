import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_129
  (a : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) :
  a = -2 := by

  field_simp at h₁ <;>
  all_goals linarith[h₁]