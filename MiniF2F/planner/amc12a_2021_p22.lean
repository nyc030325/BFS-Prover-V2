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


theorem amc12a_2021_p22
  (a b c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^3 + a * x^2 + b * x + c)
  (h₁ : f⁻¹' {0} = {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)}) :
  a * b * c = 1 / 32 := by'

  suffices h_roots_are_distinct : Real.cos (2 * Real.pi / 7) ≠ Real.cos (4 * Real.pi / 7) ∧ Real.cos (2 * Real.pi / 7) ≠ Real.cos (6 * Real.pi / 7) ∧ Real.cos (4 * Real.pi / 7) ≠ Real.cos (6 * Real.pi / 7)
  suffices h_a_vieta : a = -(Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7))
  suffices h_b_vieta : b = Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) + Real.cos (2 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7)
  suffices h_c_vieta : c = -(Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7))
  suffices h_cos_symmetry_1 : Real.cos (12 * Real.pi / 7) = Real.cos (2 * Real.pi / 7)
  suffices h_cos_symmetry_2 : Real.cos (10 * Real.pi / 7) = Real.cos (4 * Real.pi / 7)
  suffices h_cos_symmetry_3 : Real.cos (8 * Real.pi / 7) = Real.cos (6 * Real.pi / 7)
  suffices hz_ne_one : Complex.exp (2 * Real.pi * Complex.I / 7) ≠ 1
  suffices hz_pow_7_eq_one : (Complex.exp (2 * Real.pi * Complex.I / 7)) ^ 7 = 1
  suffices h_geom_sum_formula : (∑ k in (Finset.range 7 : Finset ℕ), (Complex.exp (2 * Real.pi * Complex.I / 7)) ^ k) = ((Complex.exp (2 * Real.pi * Complex.I / 7)) ^ 7 - 1) / (Complex.exp (2 * Real.pi * Complex.I / 7) - 1)
  suffices h_geom_sum_roots_of_unity : (∑ k in (Finset.range 7 : Finset ℕ), (Complex.exp (2 * Real.pi * Complex.I / 7)) ^ k) = 0
  suffices h_sum_re_zero : Complex.re (∑ k in (Finset.range 7 : Finset ℕ), (Complex.exp (2 * Real.pi * Complex.I / 7)) ^ k) = 0
  suffices h_sum_re_is_sum_re : Complex.re (∑ k in (Finset.range 7 : Finset ℕ), (Complex.exp (2 * Real.pi * Complex.I / 7)) ^ k) = (∑ k in (Finset.range 7 : Finset ℕ), Complex.re ((Complex.exp (2 * Real.pi * Complex.I / 7)) ^ k))
  suffices h_re_pow_is_cos : ∀ k : ℕ, Complex.re ((Complex.exp (2 * Real.pi * Complex.I / 7)) ^ k) = Real.cos (k * (2 * Real.pi / 7))
  suffices h_sum_cos_roots_of_unity : (∑ k in (Finset.range 7 : Finset ℕ), Real.cos (k * (2 * Real.pi / 7))) = 0
  suffices h_sum_cos_expanded : Real.cos 0 + Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7) + Real.cos (8 * Real.pi / 7) + Real.cos (10 * Real.pi / 7) + Real.cos (12 * Real.pi / 7) = 0
  suffices h_sum_cos_simplified : (1 : ℝ) + 2 * (Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7)) = 0
  suffices h_sum_roots_value : Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7) = -(1 : ℝ) / 2
  suffices h_prod_sum_relation_1 : 2 * (Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7)) = Real.cos (6 * Real.pi / 7) + Real.cos (2 * Real.pi / 7)
  suffices h_prod_sum_relation_2 : 2 * (Real.cos (2 * Real.pi / 7) * Real.cos (6 * Real.pi / 7)) = Real.cos (8 * Real.pi / 7) + Real.cos (4 * Real.pi / 7)
  suffices h_prod_sum_relation_3 : 2 * (Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7)) = Real.cos (10 * Real.pi / 7) + Real.cos (2 * Real.pi / 7)
  suffices h_sum_prods_eq_sum_roots : 2 * (Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) + Real.cos (2 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7)) = 2 * (Real.cos (2 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) + Real.cos (6 * Real.pi / 7))
  suffices h_sum_prods_value : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) + Real.cos (2 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) + Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) = -(1 : ℝ) / 2
  suffices h_root_3_alt_rep : Real.cos (6 * Real.pi / 7) = Real.cos (8 * Real.pi / 7)
  suffices h_prod_cos_identity : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (8 * Real.pi / 7) = (1 : ℝ) / 8
  suffices h_prod_roots_value : Real.cos (2 * Real.pi / 7) * Real.cos (4 * Real.pi / 7) * Real.cos (6 * Real.pi / 7) = (1 : ℝ) / 8
  suffices h_a_value : a = (1 : ℝ) / 2
  suffices h_b_value : b = -(1 : ℝ) / 2
  suffices h_c_value : c = -((1 : ℝ) / 8)
  suffices h_abc_product : a * b * c = ((1 : ℝ) / 2) * (-(1 : ℝ) / 2) * (-((1 : ℝ) / 8))
  
  norm_num at h_abc_product <;> exact h_abc_product
  norm_num [h_a_value, h_b_value, h_c_value, add_left_cancel_iff ]
  rw [h_c_vieta, h_prod_roots_value]
  rw [h_b_vieta,h_sum_prods_value]
  try rw [h_a_vieta, h_sum_roots_value]; ring
  simp [h_root_3_alt_rep, h_prod_cos_identity]
  replace h_cos_symmetry_3 := h_cos_symmetry_3.symm
  revert h_root_3_alt_rep h_cos_symmetry_3
  focus all_goals aesop (add simp [Finset.sum_range_succ])
  replace h_sum_prods_eq_sum_roots := eq_sub_of_add_eq h_sum_prods_eq_sum_roots
  nlinarith [cos_sq_add_sin_sq (2 * Real.pi / 7), cos_sq_add_sin_sq (4 * Real.pi / 7),
              cos_sq_add_sin_sq (8 * Real.pi / 7), Real.sin_two_pi,
              Real.sin_two_mul (4 * Real.pi / 7), Real.sin_two_mul (8 * Real.pi / 7)]
  rw [h_cos_symmetry_3]
  linarith [h_sum_roots_value]
  rewrite [h_cos_symmetry_1, h_cos_symmetry_2, h_cos_symmetry_3] at * <;>
    nlinarith
  repeat' rw [cos_add_cos]
  ring_nf
  rw [cos_add_cos] <;>
  ring <;> norm_num <;> linarith
  on_goal 1 => rw [show (6 * Real.pi / 7 : ℝ) = Real.pi - Real.pi / 7 by ring]
  apply Eq.symm <;> rw [cos_add_cos] <;> ring
  linarith
  norm_num [h_cos_symmetry_1, h_cos_symmetry_2, h_cos_symmetry_3] at h_sum_cos_expanded <;> linarith
  convert h_sum_cos_roots_of_unity using 1
  simp [Finset.sum_range_succ]
  ring_nf
  simp [h_re_pow_is_cos] at h_sum_re_is_sum_re h_sum_re_zero
  exacts [h_sum_re_zero]
  intro k_cos
  field_simp [←Complex.exp_nat_mul,Complex.exp_re]
  simp [Finset.sum_range]
  simp [h_geom_sum_roots_of_unity]
  simp [h_geom_sum_formula,hz_pow_7_eq_one]
  simp [geom_sum_eq hz_ne_one, hz_pow_7_eq_one]
  rw [← Complex.exp_nat_mul] <;> (try simp)
  rw [← Complex.exp_zero] <;>
  field_simp <;>
  ring
  on_goal 1 => simp [Complex.exp_eq_one_iff]
  intro n contra
  field_simp [mul_comm] at contra
  nth_rw 1 [eq_comm] at contra
  simp [mul_assoc, mul_comm, mul_left_comm] at contra
  cases' contra with contra contra
  norm_cast at contra <;>
  omega
  linarith [ Real.pi_pos  ]
  rw [show 8 * Real.pi / 7 = Real.pi + Real.pi / 7  by ring,
      cos_add]
  rw [show (6 * Real.pi / 7 : ℝ) = Real.pi - Real.pi / 7 by ring,
    cos_pi_sub]
  field_simp [Nat.prime_two]
  rw [show (10 * Real.pi / 7 : ℝ) = 2 * Real.pi - (4 * Real.pi / 7) by ring, cos_sub]
  simp [-cos_add]
  <;> ring
  rw [show (12 * Real.pi / 7 : ℝ) = 2 * Real.pi - 2 * Real.pi / 7 by ring,
    cos_sub] <;> try norm_num <;> ring
  have h_eq := h₁
  simp_all [Set.ext_iff]
  replace  h_eq := h_eq (cos (2 * Real.pi / 7))
  simp at h_eq <;> nlinarith [mul_self_nonneg (cos (2 * Real.pi / 7)), mul_self_nonneg (cos (4 * Real.pi / 7)), mul_self_nonneg (cos (6 * Real.pi / 7))]
  have := h₁
  on_goal 1 =>
    rw [Set.ext_iff] at this
  simp_all [Set.ext_iff]
  have this1 := this (cos (2 * Real.pi / 7))
  have this2 := this (cos (4 * Real.pi / 7))
  have this3 := this (cos (6 * Real.pi / 7))
  norm_num at this1 this2 this3 <;> ring_nf at *
  apply mul_left_cancel₀ <| sub_ne_zero_of_ne <| h_roots_are_distinct.1
  nlinarith [sq (cos (Real.pi * (2/7)) - cos (Real.pi * (4/7))), sq (cos (Real.pi * (2/7)) +
      cos (Real.pi * (6/7))), sq (cos (Real.pi * (4/7)) + cos (Real.pi * (6/7))) ]
  set s := cos (2 * Real.pi / 7) + cos (4 * Real.pi / 7) + cos (6 * Real.pi / 7)
  have p := h₀ 1
  norm_num [h₀] at p
  simp_all [h₀, Set.ext_iff, h₁]
  rcases h_roots_are_distinct with ⟨cos2_ne_cos4, cos2_ne_cos6, cos4_ne_cos6⟩
  have h4 := h₁ (cos (2 * Real.pi / 7))
  have h6 := h₁ (cos (6 * Real.pi / 7))
  simp [eq_comm] at h4 h6
  have h2 := h₁ (cos (4 * Real.pi / 7))
  simp [eq_comm, s] at *
  rw[eq_comm] at *
  replace h₀ := fun x => (h₀ x).symm
  set s' := cos (2 * Real.pi / 7)
  apply mul_right_cancel₀ (mul_ne_zero (sub_ne_zero_of_ne cos4_ne_cos6) (sub_ne_zero_of_ne cos2_ne_cos4))
  rw [← sub_eq_zero]
  let y := cos (2 * Real.pi / 7)
  replace h₁ := h₁ (-1)
  ring_nf at *
  nontriviality
  nlinarith [mul_self_pos.mpr <| sub_ne_zero_of_ne cos4_ne_cos6,
    mul_self_pos.mpr <| sub_ne_zero_of_ne cos2_ne_cos4, mul_self_pos.mpr <| sub_ne_zero_of_ne cos2_ne_cos6]
  simp [← sub_eq_zero, cos_sub_cos]
  refine ⟨?_, ?_, ?_⟩ <;> ring <;> norm_num
  apply And.intro<;>exact (sin_pos_of_pos_of_lt_pi (by positivity) <| by linarith [pi_pos]).ne'
  refine ⟨?_, ?_⟩ <;>
  exact (sin_pos_of_pos_of_lt_pi (by positivity) <|
          by nlinarith [Real.pi_pos]).ne'
  constructor <;> refine' (sin_pos_of_pos_of_lt_pi _ _).ne' <;> linarith [Real.pi_pos]