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


theorem amc12a_2008_p25
  (a b : ℕ → ℝ)
  (h₀ : ∀ n, a (n + 1) = Real.sqrt 3 * a n - b n)
  (h₁ : ∀ n, b (n + 1) = Real.sqrt 3 * b n + a n)
  (h₂ : a 100 = 2)
  (h₃ : b 100 = 4) :
  a 1 + b 1 = 1 / (2^98) := by'

  suffices h_complex_recurrence : ∀ n, (a (n + 1) : ℂ) + (b (n + 1) : ℂ) * Complex.I = (((Real.sqrt 3 : ℝ) : ℂ) + Complex.I) * ((a n : ℂ) + (b n : ℂ) * Complex.I)
  suffices h_general_term : ∀ k : ℕ, (a (k + 1) : ℂ) + (b (k + 1) : ℂ) * Complex.I = ((((Real.sqrt 3 : ℝ) : ℂ) + Complex.I) ^ k) * ((a 1 : ℂ) + (b 1 : ℂ) * Complex.I)
  suffices h_complex_base_polar : ((Real.sqrt 3 : ℝ) : ℂ) + Complex.I = (2 : ℂ) * Complex.exp (Complex.I * (Real.pi / 6))
  suffices h_complex_base_pow_99 : (((Real.sqrt 3 : ℝ) : ℂ) + Complex.I) ^ 99 = (2 : ℂ) ^ 99 * Complex.I
  suffices h_z100 : (a 100 : ℂ) + (b 100 : ℂ) * Complex.I = (2 : ℂ) + (4 : ℂ) * Complex.I
  suffices h_z1_relation : (a 100 : ℂ) + (b 100 : ℂ) * Complex.I = ((((Real.sqrt 3 : ℝ) : ℂ) + Complex.I) ^ 99) * ((a 1 : ℂ) + (b 1 : ℂ) * Complex.I)
  suffices h_z1_equation : (2 : ℂ) + (4 : ℂ) * Complex.I = ((2 : ℂ) ^ 99 * Complex.I) * ((a 1 : ℂ) + (b 1 : ℂ) * Complex.I)
  suffices h_z1_solved : (a 1 : ℂ) + (b 1 : ℂ) * Complex.I = ((2 : ℂ) + (4 : ℂ) * Complex.I) / ((2 : ℂ) ^ 99 * Complex.I)
  suffices h_z1_simplified : (a 1 : ℂ) + (b 1 : ℂ) * Complex.I = ((4 : ℂ) - (2 : ℂ) * Complex.I) / ((2 : ℂ) ^ 99)
  suffices h_z1_final_form : (a 1 : ℂ) + (b 1 : ℂ) * Complex.I = (1 : ℂ) / (2 : ℂ) ^ 97 - ((1 : ℂ) / (2 : ℂ) ^ 98) * Complex.I
  suffices h_a1_val : a 1 = 1 / (2 : ℝ) ^ 97
  suffices h_b1_val : b 1 = -1 / (2 : ℝ) ^ 98
  suffices h_sum : a 1 + b 1 = 1 / (2 : ℝ) ^ 97 - 1 / (2 : ℝ) ^ 98
  
  convert h_sum using 1 <;> norm_num
  norm_num [h_a1_val,h_b1_val,← add_sub]
  simp [← Complex.ext_iff] at h_z1_final_form
  norm_num at * <;> simp [Complex.ext_iff] at *
  convert h_z1_final_form.2 <;> norm_num
  rw [add_comm,← sub_eq_zero] at h_z1_final_form <;> simp [Complex.ext_iff] at *
  field_simp [← mul_add] 
  norm_num at * 
  linarith
  rw [h_z1_simplified] at *
  norm_num at * <;> ring_nf <;> norm_cast
  rw [h_z1_solved,← sub_eq_zero]
  field_simp [Complex.ext_iff] at h_z1_solved ⊢
  norm_cast <;> ring
  field_simp [h_z1_equation]
  rw [h_z100] at h_z1_relation
  try simpa [h_complex_base_pow_99] using h_z1_relation
  field_simp [h_z100,h_complex_base_pow_99]
  rw [← h_z100,h_general_term 99]
  rw [h_complex_base_pow_99]
  norm_num [h₂,h₃]
  rw [h_complex_base_polar]
  simp [← mul_pow,Complex.ext_iff]
  norm_num [mul_pow,← Complex.exp_nat_mul]
  norm_cast at * <;> simp [Complex.exp_re,Complex.exp_im]
  simp [show (99:ℝ) * (Real.pi/6)=16 * Real.pi+3 * Real.pi/6 by ring,Real.cos_add,Real.sin_add]
  simp [show (16:ℝ) * Real.pi = 2 * Real.pi+2 * Real.pi+2 * Real.pi+2 * Real.pi+2 * Real.pi+2 * Real.pi+2 * Real.pi+2 * Real.pi by ring, 
    show (3:ℝ)*Real.pi/6=Real.pi/2 by ring] <;> norm_num [Real.pi_ne_zero]
  simp [Complex.ext_iff] at *
  apply And.intro <;> field_simp [Complex.exp_re,Complex.exp_im,Real.sin_pi_div_two,Real.cos_pi_div_two]
  refine' Nat.rec _ _
  norm_num <;> simp [h_complex_recurrence 0,pow_zero] <;> ring
  intro n h_induction
  simp [pow_succ,mul_assoc,h_complex_recurrence (n+1),h_induction]
  ring_nf <;> simp [mul_comm _ (_ ^ _)] <;> ring
  field_simp [h₀,h₁,mul_add,add_mul]
  norm_num [Complex.ext_iff,mul_comm,mul_assoc,mul_left_comm]
  exact fun _n =>⟨by ring,by ring⟩