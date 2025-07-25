import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2019_p12 (x y : ℕ) (h₀ : x ≠ 1 ∧ y ≠ 1)
    (h₁ : Real.log x / Real.log 2 = Real.log 16 / Real.log y) (h₂ : x * y = 64) :
    (Real.log (x / y) / Real.log 2) ^ 2 = 20 := by

  cases' x with x <;> cases' y with y <;> norm_cast at *
  all_goals field_simp [show (16 : ℝ) = 2 ^ 4 by norm_cast] at * <;> aesop
  have : x < 64 := by nlinarith [h₂]
  interval_cases x <;> rw [mul_comm] at h₂ <;> try omega
  all_goals
    have : y < 64 := by nlinarith
    interval_cases y <;> norm_num1 at *
  any_goals field_simp [show Real.log 32 = Real.log (2 ^ 5) by norm_num, show Real.log 16 = Real.log (2 ^ 4) by norm_cast, show Real.log 8 = Real.log (2 ^ 3) by norm_cast, show Real.log 4 = Real.log (2 ^ 2) by norm_cast, Real.log_pow] at * <;> nlinarith [Real.log_pos one_lt_two]