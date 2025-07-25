import Mathlib
open BigOperators Real Nat Topology

theorem algebra_ineq_nto1onlt2m1on
  (n : ℕ)
  (h₀ : 1 < n) :
  (n : ℝ) ^ (1 / n : ℝ) < 2 - 1 / n := by

  cases' n with n n₁ n₂
  norm_num at *  <;> aesop
  field_simp [_root_.pow_one]
  field_simp [Real.rpow_def_of_pos] <;> norm_num
  rcases n with (_|_|n)
  all_goals simp [exp_lt_exp]
  all_goals ring_nf <;> norm_num at h₀ ⊢
  all_goals rw [← Real.exp_log (zero_lt_two' ℝ)]; norm_num
  any_goals field_simp [exp_log]
  all_goals rw [← Real.log_lt_log_iff] <;> norm_num
  rw [← sub_pos]
  rotate_left
  rotate_left
  any_goals positivity
  apply lt_of_le_of_lt
  apply le_of_sub_nonneg
  rotate_left
  have h₁ : 0 < (n : ℝ) + 1 := by linarith
  rw [Real.lt_log_iff_exp_lt]
  on_goal 2 => positivity
  rotate_left
  exact Real.log (3 / 2)
  nth_rw 1 [← sub_pos]
  all_goals norm_num [Real.exp_log]
  on_goal 3 => rw [div_lt_div_iff] <;> nlinarith
  on_goal 1 => rw [div_lt_iff] <;> norm_num
  on_goal 2 => rw [div_le_iff]
  on_goal 1 => rw [← sub_pos]
  repeat' positivity
  all_goals have := Real.log_pos (by norm_num1 : (1 : ℝ) < 3 / 2)
  on_goal 2 => induction n
  rotate_left
  any_goals aesop (add simp True)
  any_goals rw [← sub_nonneg] at *
  any_goals rw [← sub_pos]; ring_nf
  all_goals field_simp [mul_comm] at *
  repeat' rw [← Real.log_rpow]
  any_goals norm_num[Real.log_le_log_iff]
  on_goal 2 => apply Real.log_lt_log <;> norm_num
  rw [Real.log_le_log_iff] <;> norm_cast
  any_goals positivity
  simp [Real.log_le_iff_le_exp] at *
  rw [le_div_iff (by positivity)]
  clear a
  norm_cast <;> norm_num
  induction' n with _ hn <;> simp [pow_succ, mul_add, add_mul] at *
  simp_all [pow_add, pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : Nat) < 2) ‹_›, pow_pos (by norm_num : (0 : Nat) < 3) ‹_›]