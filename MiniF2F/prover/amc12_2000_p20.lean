import Mathlib
open BigOperators Real Nat Topology

theorem amc12_2000_p20
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x + 1/y = 4)
  (h₂ : y + 1/z = 1)
  (h₃ : z + 1/x = 7/3) :
  x*y*z = 1 := by

  rcases h₀ with ⟨cx, cy, cz⟩
  field_simp [cx, cy, cz] at h₁ h₂ h₃ ⊢ <;>
  nlinarith [mul_pos (mul_pos cx cy) (mul_pos cy cz), mul_pos (mul_pos cx cy) cz]