import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_288
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < 0 ∧ y < 0)
  (h₁ : abs y = 6)
  (h₂ : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15)
  (h₃ : Real.sqrt (x^2 + y^2) = Real.sqrt n) :
  n = 52 := by

  rcases abs_cases y with y_lt | y_ge <;> simp_all
  all_goals field_simp [sqrt_eq_iff_sq_eq] at *; norm_cast at *
  norm_num at * <;> ring
  norm_num [← NNReal.coe_inj] at * <;> nlinarith