import Mathlib
open BigOperators Real Nat Topology

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by

  by_cases h_nf : x ^ 2 - 10 * x - 29 = 0 <;> by_cases h_d : x ^ 2 - 10 * x - 45 = 0 <;> by_cases h_c : x ^ 2 - 10 * x - 69 = 0 <;> field_simp [h_nf, h_d, h_c] at h₄ <;> nlinarith