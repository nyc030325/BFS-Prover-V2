import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2020_p10
  (n : ℕ)
  (h₀ : 1 < n)
  (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) :
  (Nat.digits 10 n).sum = 13 := by

  rcases n with (_ | _ | n) <;> try simp_all
  field_simp [logb] at h₁
  field_simp [show (16 : ℝ) = 2 ^ 4 by norm_num1, Real.log_pow] at h₁
  rw [← sub_eq_zero] at h₁
  ring_nf at h₁ ⊢
  field_simp [mul_assoc,mul_comm,mul_left_comm] at h₁
  rw [← sub_eq_zero] at h₁
  field_simp [show (4 : ℝ) = 2 ^ 2 by norm_num] at h₁
  ring_nf at h₁ ⊢
  try field_simp [Real.log_mul, Real.log_inv] at h₁
  have h₂ : Real.log (2 + n) > 0 := Real.log_pos (by linarith)
  ring_nf at h₁ h₂ ⊢
  field_simp [Real.log_mul, Real.log_div] at h₁
  have : Real.log 4 = Real.log (2 ^ 2) := by norm_num
  simp_all [show (4 : ℝ) = 2 ^ 2 by norm_num]
  ring_nf at *
  have h : Real.log (Real.log (2 + n)) = Real.log (Real.log 2) + Real.log 2 * 3
  any_goals nlinarith [Real.log_pos one_lt_two ]
  have h'' := congr_arg Real.exp h
  norm_num [exp_add, exp_log, exp_mul] at h''
  field_simp [Real.exp_log, Real.exp_log] at h'' <;> norm_cast at h'' ⊢
  replace h'' := congr_arg Real.exp h''
  field_simp [exp_mul, exp_log] at h'' <;>
  norm_cast at * <;>
  aesop