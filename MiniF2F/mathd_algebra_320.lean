import Mathlib
import Aesop

open BigOperators Real Nat Topology

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


theorem mathd_algebra_320
  (x : ℝ)
  (a b c : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 ≤ x)
  (h₁ : 2 * x^2 = 4 * x + 9)
  (h₂ : x = (a + Real.sqrt b) / c)
  (h₃ : c = 2) :
  a + b + c = 26 := by'

  suffices h_standard_form : 2 * x ^ 2 - 4 * x - 9 = 0
  suffices h_discriminant : (-4 : ℝ) ^ 2 - 4 * (2 : ℝ) * (-9 : ℝ) = 88
  suffices h_x_solutions : x = (4 + Real.sqrt 88) / 4 ∨ x = (4 - Real.sqrt 88) / 4
  suffices h_sqrt_88_gt_4_sq : (88 : ℝ) > 16
  suffices h_sqrt_88_gt_4 : Real.sqrt 88 > 4
  suffices h_numerator_of_neg_sol_is_neg : (4 : ℝ) - Real.sqrt 88 < 0
  suffices h_neg_sol_is_neg : ((4 : ℝ) - Real.sqrt 88) / 4 < 0
  suffices h_x_is_pos_root : x = (4 + Real.sqrt 88) / 4
  suffices h_sqrt_88_decomp : (88 : ℝ) = 4 * 22
  suffices h_sqrt_88_simp : Real.sqrt 88 = Real.sqrt (4 * 22)
  suffices h_sqrt_88_pull_out_4 : Real.sqrt (4 * 22) = Real.sqrt 4 * Real.sqrt 22
  suffices h_sqrt_88_final : Real.sqrt 88 = 2 * Real.sqrt 22
  suffices h_x_subst_sqrt : x = (4 + 2 * Real.sqrt 22) / 4
  suffices h_x_factor_numerator : x = (2 * (2 + Real.sqrt 22)) / 4
  suffices h_x_simplified : x = (2 + Real.sqrt 22) / 2
  suffices h_x_from_hypotheses : x = ((a : ℝ) + Real.sqrt (b : ℝ)) / (c : ℝ)
  suffices h_x_from_hypotheses_c_subst : x = ((a : ℝ) + Real.sqrt (b : ℝ)) / 2
  suffices h_equated_forms : ((a : ℝ) + Real.sqrt (b : ℝ)) / 2 = (2 + Real.sqrt 22) / 2
  suffices h_numerators_equal : (a : ℝ) + Real.sqrt (b : ℝ) = 2 + Real.sqrt 22
  suffices h_isolate_sqrt_b : Real.sqrt (b : ℝ) = ((2 : ℝ) - (a : ℝ)) + Real.sqrt 22
  suffices h_squared_both_sides : (Real.sqrt (b : ℝ)) ^ 2 = (((2 : ℝ) - (a : ℝ)) + Real.sqrt 22) ^ 2
  suffices h_lhs_squared_simp : (Real.sqrt (b : ℝ)) ^ 2 = (b : ℝ)
  suffices h_rhs_squared_expanded : (((2 : ℝ) - (a : ℝ)) + Real.sqrt 22) ^ 2 = ((2 : ℝ) - (a : ℝ)) ^ 2 + 22 + 2 * ((2 : ℝ) - (a : ℝ)) * Real.sqrt 22
  suffices h_eq_after_squaring : (b : ℝ) = ((2 : ℝ) - (a : ℝ)) ^ 2 + 22 + 2 * ((2 : ℝ) - (a : ℝ)) * Real.sqrt 22
  suffices h_isolate_irrational_term : (b : ℝ) - ((2 : ℝ) - (a : ℝ)) ^ 2 - 22 = 2 * ((2 : ℝ) - (a : ℝ)) * Real.sqrt 22
  suffices h_lhs_is_rational : ∃ q : ℚ, (b : ℝ) - ((2 : ℝ) - (a : ℝ)) ^ 2 - 22 = ↑q
  suffices h_sqrt_22_is_irrational : Irrational (Real.sqrt 22)
  suffices h_rational_factor_must_be_zero : 2 * ((2 : ℝ) - (a : ℝ)) = 0
  suffices h_a_minus_2_is_zero : (2 : ℝ) - (a : ℝ) = 0
  suffices a_val : a = 2
  suffices h_subst_a_into_isolated_eq : (b : ℝ) - ((2 : ℝ) - (2 : ℝ)) ^ 2 - 22 = 2 * ((2 : ℝ) - (2 : ℝ)) * Real.sqrt 22
  suffices h_subst_a_simplifies_to : (b : ℝ) - 0 - 22 = 0
  suffices b_val : b = 22
  suffices c_val : c = 2
  suffices final_sum : (a : ℕ) + b + c = 2 + 22 + 2

  exact final_sum.trans (by norm_cast)
  rw [a_val,b_val,c_val]
  assumption
            <;> norm_cast
  simp_all [sub_eq_zero] <;> norm_cast at * <;> linarith
  simp at h_subst_a_into_isolated_eq
  norm_num [h_subst_a_into_isolated_eq]
  aesop
  exact_mod_cast( by linarith : (a : ℝ) = 2 )
  linarith
  obtain ⟨q, h_q⟩ :=  h_lhs_is_rational
  rw [h_q] at h_isolate_irrational_term
  by_contra h_nonzero
  apply h_sqrt_22_is_irrational
  exact ⟨q / (2 * (2 - a) : ℚ), by field_simp [h_isolate_irrational_term, mul_comm]⟩
  refine irrational_sqrt_ofNat_iff.mpr ?_
  on_goal 1 => by_contra h_sq
  obtain ⟨n, hn22⟩ := h_sq
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := ( Nat.even_or_odd n ) <;> ring_nf at hn22 ⊢ <;> omega
  exact ⟨ (b - (2 - a) ^ 2 - 22 : ℤ), by simp ⟩
  linarith
  rw [h_lhs_squared_simp, h_rhs_squared_expanded] at h_squared_both_sides
  assumption
  ring_nf
  simp [sq, pow_two]
  <;> norm_num
  <;>ring
  simp
  rw [h_isolate_sqrt_b]
  nlinarith
  field_simp at h_equated_forms <;> try simp_all
  aesop (add simp [div_eq_mul_inv])
  simp_all [add_assoc, mul_assoc] <;>
  ring
  exact h₂
  convert h_x_factor_numerator using 1 <;> ring
  on_goal 1 => convert h_x_subst_sqrt using 1 <;> ring
  rw [h_x_is_pos_root, h_sqrt_88_final]
  rw [h_sqrt_88_simp, h_sqrt_88_pull_out_4]  <;> simp [show √4 = √(2 * 2) by ring] <;> norm_num
  apply Real.sqrt_mul (by norm_num)
  rw [h_sqrt_88_decomp]
  ring
  <;> norm_cast
  cases h_x_solutions <;> (first | linarith | nlinarith)
  exact div_neg_of_neg_of_pos h_numerator_of_neg_sol_is_neg (by linarith)
  linarith![h_sqrt_88_gt_4]
  iterate 1 refine Real.lt_sqrt_of_sq_lt ?_ <;> norm_num1 at *
  norm_num <;> decide
  simp [← sub_eq_zero, ← mul_eq_mul_right_iff] at *
  on_goal 1 => ring_nf
  rw [Real.sq_sqrt, ← sub_eq_zero] <;>norm_num
  nlinarith 
    <;> rw [h₃] at *
    <;> field_simp at *
    <;> nlinarith
  norm_num [mul_pow, ← h₂]
  linarith [ sq_nonneg ((x - 2 : ℝ) ^ 2) ]