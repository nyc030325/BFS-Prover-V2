import Mathlib
import Aesop

open BigOperators Real Nat Topology Int

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Lean Parser Elab Tactic

elab "focus' " tacs:tacticSeq1Indented : tactic => do
  match tacs.raw[0] with
  | .node _ _ args =>
    for tac in args do
      if tac[0].isMissing then continue
      focus (evalTactic tac)
  | _ => unreachable!

macro "by' " tacs:tacticSeq1Indented : term =>
  `(term| by focus' $tacs)


theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∑ k in (Finset.Icc (2 : ℕ) 10000), (1 / Real.sqrt k) < 198 := by'

  suffices h_inequality : ∀ k : ℕ, 2 ≤ k → (1 : ℝ) / Real.sqrt (k : ℝ) < (2 : ℝ) * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))
  suffices h_sum_bound : ∑ k in (Finset.Icc (2 : ℕ) 10000 : Finset ℕ), (1 : ℝ) / Real.sqrt (k : ℝ) < ∑ k in (Finset.Icc (2 : ℕ) 10000 : Finset ℕ), (2 : ℝ) * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1))
  suffices h_telescoping_sum : ∑ k in (Finset.Icc (2 : ℕ) 10000 : Finset ℕ), (2 : ℝ) * (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) - 1)) = (2 : ℝ) * (Real.sqrt (10000 : ℝ) - Real.sqrt (1 : ℝ))
  suffices h_sqrt_10000 : Real.sqrt (10000 : ℝ) = (100 : ℝ)
  suffices h_sqrt_1 : Real.sqrt (1 : ℝ) = (1 : ℝ)
  suffices h_rhs_value : (2 : ℝ) * ((100 : ℝ) - (1 : ℝ)) = (198 : ℝ)

  nlinarith
  ring
  <;> native_decide
  simp [Real.sqrt]
  rw [ Real.sqrt_eq_iff_mul_self_eq] <;> norm_cast <;> decide
  group
  have h_cancellation  : ∀ (n : ℕ), 2 ≤ n → (∑ k : ℕ in Finset.Icc 2 n, (√(k : ℝ) * 2 - √(-1 + k) * 2)) = √n * 2 - √1 * 2
  intro n two_le_n
  induction' two_le_n with nn h_ind
  norm_num
  <;> ring
  cases' h_ind with _ h_ind
  norm_num [Finset.sum_Icc_succ_top, Nat.succ_eq_add_one]
  ring_nf <;> linarith
  try rw [Finset.sum_Icc_succ_top]
  field_simp [Finset.sum_Icc_succ_top, *]
  repeat' linarith
  convert h_cancellation 10000 (by norm_num1) using 1 <;> norm_cast
  apply Finset.sum_lt_sum <;>aesop
  have := h_inequality i left
  next => apply le_of_lt this
  refine ⟨2, ⟨(by norm_num), (by norm_num)⟩, ?_⟩
  convert h_inequality 2 (by norm_num) <;> norm_num
  rintro n (_ : 2 ≤ n)
  have : 0 ≤ √(n-1) := Real.sqrt_nonneg _
  rw [div_lt_iff'] <;> norm_cast <;> ring_nf
  field_simp [this]
  nth_rw 1 [← Real.sqrt_mul (by positivity)]
  have hb : (0 : ℝ) ≤ n
  positivity
  apply lt_of_pow_lt_pow <;> norm_cast
  positivity
  simp [mul_assoc]
  apply pow_lt_pow_left <;> norm_num
  rcases n with (_ | _ | n)
  any_goals norm_num at *
  contradiction
  apply lt_of_le_of_lt <;> norm_cast
  cases' n with n <;> simp [Int.subNatNat] at * <;> norm_num
  nlinarith [Real.sq_sqrt two_pos.le, Real.sqrt_nonneg (2 : ℝ)]
  nlinarith [Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ n + 1 + 1),
    Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ n + 1 + 1 + 1), norm_num]
  positivity
  linarith
  positivity