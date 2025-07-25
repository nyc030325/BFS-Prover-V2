import Mathlib
open BigOperators Real Nat Topology

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem amc12a_2020_p15
  (a b : ℂ)
  (h₀ : a^3 - 8 = 0)
  (h₁ : b^3 - 8 * b^2 - 8 * b + 64 = 0) :
  Complex.abs (a - b) ≤ 2 * Real.sqrt 21 := by
  
  have ha1 : a ^ 3 = 8
  any_goals simp [sub_eq_zero, *] at *
  simp_all [Complex.ext_iff]
  rw [ ← sub_eq_zero] at ha1
  replace h₁ : (b - 8) * (b ^ 2 - 8) = 0 := by linear_combination h₁
  rw [mul_comm] at h₁
  replace ha1 : a ^ 3 = 8 := by linear_combination ha1
  have hab : a = 2 ∨ a = -1 + Complex.I * Real.sqrt 3 ∨ a = -1 - Complex.I * Real.sqrt 3
  field_simp [mul_comm] at h₁
  simp [← sub_eq_zero, ← mul_eq_mul_right_iff]
  ring_nf at *
  have ha2 : a ^ 3 = 8 := ha1
  on_goal 1 => simp_all [pow_three]
  field_simp [ha2] at * <;> ring
  field_simp [Complex.ext_iff] at *
  field_simp [pow_two] at *
  any_goals aesop (add simp [Complex.abs])
  any_goals simp [Complex.normSq]
  any_goals nlinarith [sq_nonneg (b.re^2 + b.im^2 - 8), sq_nonneg b.re, sq_nonneg b.im]
  any_goals simp [sub_eq_zero, add_comm] at *
  any_goals simp only [sq, Complex.ext_iff] at *
  all_goals aesop (add simp [sq])
  any_goals ring_nf at *; norm_num
  any_goals simp_all [pow_three]
  all_goals rw [Real.sqrt_le_left (by positivity)]; ring_nf
  any_goals nlinarith [sq_nonneg (b.im - √3 * b.re), Real.sqrt_nonneg 21, Real.sq_sqrt (by norm_cast : (0 : ℝ) ≤ 21)]
  repeat' cases' right_1 <;> simp_all
  all_goals aesop (add simp [sq])
  any_goals nlinarith