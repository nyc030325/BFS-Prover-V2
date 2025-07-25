import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2021_p18
  (z : ℂ)
  (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z^2 + 1) + 31) :
  z + 6 / z = -2 := by

  cases' z with x y <;> simp [Complex.normSq] at h₀ ⊢
  simp_all [sq, Complex.ext_iff]
  field_simp [Complex.div_re, Complex.div_im] at h₀ ⊢
  have h₁: x * x + y * y = 6 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 2)]
  field_simp [h₁, add_assoc] <;> exact ⟨by nlinarith, by nlinarith⟩