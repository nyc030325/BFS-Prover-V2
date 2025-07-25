import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_276
  (a b : ℤ)
  (h₀ : ∀ x : ℝ, 10 * x^2 - x - 24 = (a * x - 8) * (b * x + 3)) :
  a * b + b = 12 := by

  on_goal 1 =>
    have E1 := h₀ 0
    have E2 := h₀ 1
    have E3 := h₀ 2
    norm_cast at E1 E2 E3
  repeat rw [Int.subNatNat_eq_coe] at *
  norm_num at E1 E2 E3 <;> try omega
  classical
      have : b < 15 := by nlinarith
      have : b > -15 := by nlinarith
      interval_cases b <;> omega