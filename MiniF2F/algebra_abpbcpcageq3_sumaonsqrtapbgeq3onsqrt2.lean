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


theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 3 ≤ a * b + b * c + c * a) :
  3 / Real.sqrt 2 ≤ a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) := by'

  suffices h_p_sq_expand : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a)
  suffices h_p_sq_ge_3q : (a + b + c)^2 ≥ 3 * (a * b + b * c + c * a)
  suffices h_p_sq_ge_9 : (a + b + c)^2 ≥ 3 * 3
  suffices h_p_ge_3 : 3 ≤ a + b + c
  suffices h_S_rewritten : a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) = a^2 / (a * Real.sqrt (a + b)) + b^2 / (b * Real.sqrt (b + c)) + c^2 / (c * Real.sqrt (c + a))
  suffices h_sum_of_squares_nonneg : (a * (b * Real.sqrt (b + c)) - b * (a * Real.sqrt (a + b)))^2 / ((a * Real.sqrt (a + b)) * (b * Real.sqrt (b + c))) + (a * (c * Real.sqrt (c + a)) - c * (a * Real.sqrt (a + b)))^2 / ((a * Real.sqrt (a + b)) * (c * Real.sqrt (c + a))) + (b * (c * Real.sqrt (c + a)) - c * (b * Real.sqrt (b + c)))^2 / ((b * Real.sqrt (b + c)) * (c * Real.sqrt (c + a))) ≥ 0
  suffices h_identity : (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a)) * (a^2 / (a * Real.sqrt (a + b)) + b^2 / (b * Real.sqrt (b + c)) + c^2 / (c * Real.sqrt (c + a))) - (a + b + c)^2 = (a * (b * Real.sqrt (b + c)) - b * (a * Real.sqrt (a + b)))^2 / ((a * Real.sqrt (a + b)) * (b * Real.sqrt (b + c))) + (a * (c * Real.sqrt (c + a)) - c * (a * Real.sqrt (a + b)))^2 / ((a * Real.sqrt (a + b)) * (c * Real.sqrt (c + a))) + (b * (c * Real.sqrt (c + a)) - c * (b * Real.sqrt (b + c)))^2 / ((b * Real.sqrt (b + c)) * (c * Real.sqrt (c + a)))
  suffices h_diff_nonneg : (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a)) * (a^2 / (a * Real.sqrt (a + b)) + b^2 / (b * Real.sqrt (b + c)) + c^2 / (c * Real.sqrt (c + a))) - (a + b + c)^2 ≥ 0
  suffices h_titu_ineq : a^2 / (a * Real.sqrt (a + b)) + b^2 / (b * Real.sqrt (b + c)) + c^2 / (c * Real.sqrt (c + a)) ≥ (a + b + c)^2 / (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))
  suffices h_S_ge_p_sq_div_D : a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) ≥ (a + b + c)^2 / (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))
  suffices h_sum_of_squares_nonneg : (Real.sqrt a * (Real.sqrt b * Real.sqrt (b + c)) - Real.sqrt b * (Real.sqrt a * Real.sqrt (a + b)))^2 + (Real.sqrt a * (Real.sqrt c * Real.sqrt (c + a)) - Real.sqrt c * (Real.sqrt a * Real.sqrt (a + b)))^2 + (Real.sqrt b * (Real.sqrt c * Real.sqrt (c + a)) - Real.sqrt c * (Real.sqrt b * Real.sqrt (b + c)))^2 ≥ 0
  suffices h_identity : (a + b + c) * (a * (a + b) + b * (b + c) + c * (c + a)) - (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))^2 = (Real.sqrt a * (Real.sqrt b * Real.sqrt (b + c)) - Real.sqrt b * (Real.sqrt a * Real.sqrt (a + b)))^2 + (Real.sqrt a * (Real.sqrt c * Real.sqrt (c + a)) - Real.sqrt c * (Real.sqrt a * Real.sqrt (a + b)))^2 + (Real.sqrt b * (Real.sqrt c * Real.sqrt (c + a)) - Real.sqrt c * (Real.sqrt b * Real.sqrt (b + c)))^2
  suffices h_diff_nonneg : (a + b + c) * (a * (a + b) + b * (b + c) + c * (c + a)) - (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))^2 ≥ 0
  suffices h_D_sq_le_by_CS : (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))^2 ≤ (a + b + c) * (a * (a + b) + b * (b + c) + c * (c + a))
  suffices h_D_denom_sum_in_p_q : a * (a + b) + b * (b + c) + c * (c + a) = (a + b + c)^2 - (a * b + b * c + c * a)
  suffices h_D_sq_upper_bound : (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))^2 ≤ (a + b + c) * ((a + b + c)^2 - (a * b + b * c + c * a))
  suffices h_middle : (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a))^2 ≥ ((a + b + c)^2)^2 / (a * Real.sqrt (a + b) + b * Real.sqrt (b + c) + c * Real.sqrt (c + a))^2
  suffices h_S_sq_ge : (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a))^2 ≥ ((a + b + c)^2)^2 / ((a + b + c) * ((a + b + c)^2 - (a * b + b * c + c * a)))
  suffices h_equal : ((a + b + c)^2)^2 / (a + b + c) = (a + b + c)^3
  suffices h_S_sq_ge_simplified : (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a))^2 ≥ (a + b + c)^3 / ((a + b + c)^2 - (a * b + b * c + c * a))
  suffices h_target_sq : (3 / Real.sqrt 2)^2 = (9 : ℝ) / 2
  suffices h_final_poly_is_nonneg : 0 ≤ ((a + b + c) - 3)^2 * (2 * (a + b + c) + 3)
  suffices h_poly_factorization : 2 * (a + b + c)^3 - 9 * (a + b + c)^2 + 27 = ((a + b + c) - 3)^2 * (2 * (a + b + c) + 3)
  suffices h_final_poly : 0 ≤ 2 * (a + b + c)^3 - 9 * (a + b + c)^2 + 27
  suffices h_ineq_poly_form : 0 ≤ 2 * (a + b + c)^3 - 9 * (a + b + c)^2 + 9 * (a * b + b * c + c * a)
  suffices h_ineq_cross_mul : 2 * (a + b + c)^3 ≥ 9 * ((a + b + c)^2 - (a * b + b * c + c * a))
  suffices h_p_sq_minus_q_pos : 0 < (a + b + c)^2 - (a * b + b * c + c * a)
  suffices h_sufficient_ineq : (a + b + c)^3 / ((a + b + c)^2 - (a * b + b * c + c * a)) ≥ (9 : ℝ) / 2
  suffices h_final : (a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a))^2 ≥ (9 : ℝ) / 2
  
  have ha_ge : 0 ≤ a / √(a + b) + b / √(b + c) + c / √(c + a) :=
    add_nonneg (add_nonneg (div_nonneg (by linarith) (by positivity)) (div_nonneg (by linarith) (by positivity))) (div_nonneg (by linarith) (by positivity))
  apply le_of_pow_le_pow_left two_ne_zero (by positivity)
  linarith
  linarith
  rw [ge_iff_le, div_le_div_iff] <;> linarith
  nlinarith only [h₁,h_p_sq_ge_3q]
  linarith
  linarith
  linarith
  linarith [h_sum_of_squares_nonneg]
  positivity
  norm_num [mul_pow, div_pow, sq_sqrt]
  convert h_S_sq_ge using 1
  symm
  conv => lhs; rw [div_mul_eq_div_div]
  rw [h_equal]
  exact by (field_simp; ring)
  apply ge_trans h_middle ?_
  gcongr
  apply sq_pos_of_pos
  aesop
  positivity
  apply le_of_sub_nonneg
  have h_denom_pos : 0 < a * √(a + b) + b * √(b + c) + c * √(c + a)
  obtain ⟨h_a_pos, h_b_pos, h_c_pos⟩ := h₀
  positivity
  have h_num_nonneg : 0 ≤ (a + b + c) ^ 2 / (a * √(a + b) + b * √(b + c) + c * √(c + a)) := by positivity
  have h_row7_ge1_sub1 : (a / √(a + b) + b / √(b + c) + c / √(c + a)) ^ 2 - ((a + b + c) ^ 2 / (a * √(a + b) + b * √(b + c) + c * √(c + a))) ^ 2 ≥ 0
  apply sub_nonneg_of_le
  refine' pow_le_pow_left h_num_nonneg h_S_ge_p_sq_div_D _
  repeat aesop
  calc
    _ ≤ _ := h_D_sq_le_by_CS
    _ = (a + b + c) * ((a + b + c) ^ 2 - (a * b + b * c + c * a)) := by rw[h_D_denom_sum_in_p_q]
    _ = _ := by ring
  ring
  linarith
  rw [h_identity]
  apply h_sum_of_squares_nonneg
  ring_nf
  simp [(Real.sq_sqrt (by linarith: 0 ≤ a )), (Real.sq_sqrt (by linarith: 0 ≤ b)),
      (Real.sq_sqrt (by linarith: 0 ≤ c))]
  rw [ Real.sq_sqrt, Real.sq_sqrt ,Real.sq_sqrt]
  ring
  nlinarith [Real.sqrt_pos.2 h₀.2.2]
  apply add_nonneg <;> linarith
  linarith [h₀.1]
  positivity
  nlinarith [h_S_rewritten]
  rw [ge_iff_le]
  have h_geometric  : 0 < a * √(a + b) + b * √(b + c) +  c * √(c + a)
  obtain ⟨h_a_pos, h_b_pos, h_c_pos⟩ := h₀
  positivity
  rw [div_le_iff (h_geometric)] <;> nlinarith
  nlinarith
  simp [add_mul, h₀.1, h₀.2.1, h₀.2.2]
  obtain ⟨a_pos, b_pos, c_pos⟩ := h₀
  field_simp
  ring
  apply add_nonneg  <;> try positivity
  apply add_nonneg  <;> try positivity
  apply div_nonneg
  apply sq_nonneg
  apply_rules [mul_nonneg,mul_pos,Real.sqrt_nonneg,Real.sqrt_pos.2] <;> try linarith
  apply div_nonneg
  apply sq_nonneg
  apply_rules [mul_nonneg,mul_pos,Real.sqrt_nonneg,Real.sqrt_pos.2] <;> try linarith
  apply div_nonneg
  apply sq_nonneg
  apply_rules [mul_nonneg,mul_pos,Real.sqrt_nonneg,Real.sqrt_pos.2] <;> try linarith
  rw[div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv]
  obtain ⟨_, b_pos, c_pos⟩ := h₀ <;> field_simp <;> ring
  nlinarith [sq_nonneg ( a - b), sq_nonneg (c - a ) ,sq_nonneg (b - c)]
  nlinarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h₁]
  exacts [by ring ]