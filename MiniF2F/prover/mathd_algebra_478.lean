import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_478
  (b h v : ℝ)
  (h₀ : 0 < b ∧ 0 < h ∧ 0 < v)
  (h₁ : v = 1 / 3 * (b * h))
  (h₂ : b = 30)
  (h₃ : h = 13 / 2) :
  v = 65 := by

  field_simp [← mul_assoc, h₀, h₂, h₃] at h₁ <;> linarith