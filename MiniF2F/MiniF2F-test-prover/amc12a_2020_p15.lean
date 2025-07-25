import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2020_p15
  (a b : ℂ)
  (h₀ : a^3 - 8 = 0)
  (h₁ : b^3 - 8 * b^2 - 8 * b + 64 = 0) :
  Complex.abs (a - b) ≤ 2 * Real.sqrt 21 := by

  have f
  exact h₀
  have : a ^ 3 = 8 := by linear_combination h₀
  have h : b ^ 2 * (b - 8) - 8 * (b - 8) = 0 := by linear_combination h₁
  have h₁ : (a - 2) * (a ^ 2 + 2 * a + 4) = 0 := by linear_combination this - a ^ 3
  simp_all [sq, sub_eq_zero]
  cases' h₁ with h₁ h₁
  all_goals aesop (add simp Complex.abs_eq_sqrt_sq_add_sq)
  any_goals rw [ Real.sqrt_le_left] <;> norm_num
  any_goals norm_num [mul_pow]
  any_goals try positivity
  any_goals norm_cast  at *
  any_goals simp [sq, sub_eq_add_neg]
  all_goals simp [sq, sub_eq_add_neg] at *
  all_goals norm_cast at *
  conv => lhs; ring
  aesop (add simp [sq])
  cases' b with x y
  simp [ Complex.ext_iff ] at *
  any_goals (norm_cast at *; repeat' nlinarith)
  any_goals simp_all [sq]
  any_goals simp [sq, mul_add, mul_comm, mul_left_comm] at *
  any_goals simp [pow_three] at *
  cases h_1.2 <;> aesop
  any_goals norm_cast at *
  nlinarith
  any_goals norm_num
  repeat' nlinarith [sq_nonneg x, sq_nonneg (x - 2), sq_nonneg (x + 2)]
  any_goals simp [Complex.ext_iff] at * <;> norm_cast
  repeat' nlinarith [sq_nonneg (a.re - 2), sq_nonneg (a.re + 2),
                sq_nonneg (a.im - 2), sq_nonneg (a.im + 2)]
  nlinarith [ sq_nonneg (a.re - b.re),sq_nonneg (a.re + b.re),
                  sq_nonneg (a.im + b.im), sq_nonneg (a.im - b.im),
                  h₁.1, h₁_1.2]