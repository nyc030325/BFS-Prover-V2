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


theorem aime_1995_p7
  (k m n : ℕ)
  (t : ℝ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 1)
  (h₂ : (1 + Real.sin t) * (1 + Real.cos t) = 5/4)
  (h₃ : (1 - Real.sin t) * (1- Real.cos t) = m/n - Real.sqrt k):
  k + m + n = 27 := by'

  suffices h_S_sq_identity : (Real.sin t + Real.cos t) ^ 2 = 1 + 2 * Real.sin t * Real.cos t
  suffices h_P_in_terms_of_S : Real.sin t * Real.cos t = ((Real.sin t + Real.cos t) ^ 2 - 1) / (2 : ℝ)
  suffices h_S_substitution : (Real.sin t + Real.cos t) + ((Real.sin t + Real.cos t) ^ 2 - 1) / (2 : ℝ) = (1 : ℝ)  / 4
  suffices h_S_quadratic_form : 2 * (Real.sin t + Real.cos t) ^ 2 + 4 * (Real.sin t + Real.cos t) - 3 = 0
  suffices h_discriminant : (4 : ℝ) ^ 2 - 4 * (2 : ℝ) * (-3 : ℝ) = 40
  suffices h_S_solutions : Real.sin t + Real.cos t = ((-4) + Real.sqrt 40) / (4 : ℝ) ∨ Real.sin t + Real.cos t = ((-4) - Real.sqrt 40) / (4 : ℝ)
  suffices h_sqrt_40_simp : Real.sqrt 40 = 2 * Real.sqrt 10
  suffices h_S_solutions_simp : Real.sin t + Real.cos t = (-2 + Real.sqrt 10) / (2 : ℝ) ∨ Real.sin t + Real.cos t = (-2 - Real.sqrt 10) / (2 : ℝ)
  suffices h_S_bounds : -(Real.sqrt 2) ≤ Real.sin t + Real.cos t ∧ Real.sin t + Real.cos t ≤ Real.sqrt 2
  suffices h_neg_sol_lower_bound_check : (-2 - Real.sqrt 10) / (2 : ℝ) < -(Real.sqrt 2)
  suffices h_S_val : Real.sin t + Real.cos t = (-2 + Real.sqrt 10) / (2 : ℝ)
  suffices h_P_val_from_S : Real.sin t * Real.cos t = (1 : ℝ) / 4 - ((-2 + Real.sqrt 10) / (2 : ℝ))
  suffices h_P_val_simp : Real.sin t * Real.cos t = (5 - 2 * Real.sqrt 10) / (4 : ℝ)
  suffices h_expand_h₃ : 1 - (Real.sin t + Real.cos t) + Real.sin t * Real.cos t = (↑m : ℝ) / (↑n : ℝ) - Real.sqrt (↑k : ℝ)
  suffices h_subst_into_h₃ : 1 - ((-2 + Real.sqrt 10) / (2 : ℝ)) + (5 - 2 * Real.sqrt 10) / (4 : ℝ) = (↑m : ℝ) / (↑n : ℝ) - Real.sqrt (↑k : ℝ)
  suffices h_lhs_simplified : 1 - ((-2 + Real.sqrt 10) / (2 : ℝ)) + (5 - 2 * Real.sqrt 10) / (4 : ℝ) = (13 : ℝ) / 4 - Real.sqrt 10
  suffices h_main_equality : (13 : ℝ) / 4 - Real.sqrt 10 = (↑m : ℝ) / (↑n : ℝ) - Real.sqrt (↑k : ℝ)
  suffices h_rearranged_equality : (13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ) = Real.sqrt 10 - Real.sqrt (↑k : ℝ)
  suffices h_sqrt10_irrational : Irrational (Real.sqrt 10)
  suffices h_lhs_rational : ∃ q : ℚ, (13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ) = ↑q
  suffices h_sqrt_k_irrational : Irrational (Real.sqrt (↑k : ℝ))
  suffices h_irrational_arg_rearrangement : ((13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ)) + Real.sqrt (↑k : ℝ) = Real.sqrt 10
  suffices h_squaring_irrational_arg : (((13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ)) + Real.sqrt (↑k : ℝ)) ^ 2 = 10
  suffices h_expanded_square : ((13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ)) ^ 2 + (↑k : ℝ) + 2 * ((13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ)) * Real.sqrt (↑k : ℝ) = 10
  suffices h_isolate_irrational_term : 2 * ((13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ)) * Real.sqrt (↑k : ℝ) = 10 - (↑k : ℝ) - ((13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ)) ^ 2
  suffices h_rhs_rational : ∃ q : ℚ, 10 - (↑k : ℝ) - ((13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ)) ^ 2 = ↑q
  suffices h_rational_coeff_is_zero : (13 : ℝ) / 4 - (↑m : ℝ) / (↑n : ℝ) = 0
  suffices h_k_equation : 10 - (↑k : ℝ) - 0 = 0
  suffices k_val : k = 10
  suffices h_mn_cross_mul_nat : 4 * m = 13 * n
  suffices h_coprime : Nat.Coprime 13 4
  suffices m_val : m = 13
  suffices n_val : n = 4

  norm_num [k_val,m_val,n_val]
  classical
    omega
  revert h_coprime
  intro _h_coprime_13_4
  classical
    (
      have : m ∣ 13 * n := by rw [← h_mn_cross_mul_nat]; simp
      have : m ∣ 13 := Nat.Coprime.dvd_of_dvd_mul_right h₁ this
      have h_ub : m ≤ 13 := Nat.le_of_dvd (by norm_num) this
      interval_cases m <;> omega
    )
  norm_num
  field_simp [eq_div_iff] at h_rational_coeff_is_zero
  field_simp [ h₀.2.2.ne'] at h_rational_coeff_is_zero
  norm_cast at h_rational_coeff_is_zero
  simp [Int.subNatNat_eq_coe] at h_rational_coeff_is_zero <;> linarith
  simp at h_k_equation
  have hk : (k : ℝ) = 10 := by linarith
  norm_cast at hk
  simp_all [sub_eq_iff_eq_add]
  obtain ⟨q, hq⟩ := h_rhs_rational
  rw [hq] at h_isolate_irrational_term
  by_contra hcontra
  rw [mul_comm] at h_isolate_irrational_term
  apply h_sqrt_k_irrational
  simp [← h_isolate_irrational_term]
  use ↑q / (2 * (13 / 4 - (m : ℚ) / n))
  field_simp [hcontra, h_isolate_irrational_term]
  field_simp [mul_comm] at *
  field_simp [mul_comm, hcontra]
  rw [←h_isolate_irrational_term, mul_assoc]
  use 10 - k - (13 / 4 - m / n) ^ 2
  field_simp
  linarith
  rw [add_sq] at h_squaring_irrational_arg
  rw [Real.sq_sqrt (Nat.cast_nonneg k)] at h_squaring_irrational_arg
  convert h_squaring_irrational_arg using 1
  ring_nf
  rw [h_irrational_arg_rearrangement]
  norm_num
  simp_all [ Irrational, Rat.cast_inj]
  obtain ⟨q, h_q⟩ := h_lhs_rational
  rw [h_q] at h_rearranged_equality
  by_contra h_rational
  simp only [irrational_iff_ne_rational] at h_rational
  push_neg  at h_rational
  obtain ⟨a, b, h_rational⟩ := h_rational
  have h_rational' := h_rational
  apply h_sqrt10_irrational
  exists (((13 / 4) - ↑m / ↑n) + ↑a / ↑b)
  norm_cast at* <;> try { aesop }
  exact ⟨(13 / 4 - m / n), by field_simp⟩
  refine irrational_sqrt_natCast_iff.mpr ?_
  on_goal 1 => by_contra h_square_10
  obtain ⟨x, hx⟩ := h_square_10
  obtain ⟨x, rfl⟩|⟨x, rfl⟩ := Nat.even_or_odd x <;>
                  ring_nf at hx <;> norm_cast at hx <;>omega
  linarith
  rw [h_lhs_simplified] at h_subst_into_h₃
  exact h_subst_into_h₃
  linarith <;> ring
  aesop (add simp div_eq_mul_inv)
  simp [h_S_val, h_P_val_simp, sub_eq_add_neg, add_assoc]
  norm_num at * <;>linarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
  ring_nf at h_P_val_from_S ⊢ <;> linarith
  any_goals
      rw [h_P_in_terms_of_S]
      field_simp [h_S_val]
      ring <;> norm_num <;> nlinarith [Real.sqrt_pos.mpr (show 0 < 10 by norm_num), Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 10)]
  cases h_S_solutions_simp <;> linarith [(Real.sqrt_pos.2 (show (10 : ℝ) > 0 by norm_num)).le,
    Real.sqrt_nonneg 2]
  rw [div_lt_iff, ← sub_pos] <;> norm_num
  rcases h_S_solutions_simp with h_sin_cos | h_sin_cos <;> rw [h_sin_cos] at h_S_bounds <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 10), Real.sq_sqrt zero_lt_two.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)] <;> ring
  rcases h_S_solutions_simp <;>
  ring_nf at * <;>
  constructor <;> nlinarith [Real.sqrt_pos.2 zero_lt_two, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  convert h_S_solutions using 2 <;> rw [h_sqrt_40_simp] <;> ring
  field_simp[show (40 : ℝ) = 2 * 2 * (10 : ℝ) by norm_num ]
  suffices H : (sin t + cos t = (-4 + Real.sqrt 40) / 4 ∨ sin t + cos t = (-4 - Real.sqrt 40) / 4)
  convert H <;> (rw [or_comm]; ring)
  rw [← sub_eq_zero] at h_S_quadratic_form
  rewrite [or_iff_not_imp_left]
  unhygienic aesop
  apply mul_right_cancel₀ (sub_ne_zero_of_ne a) <;> nlinarith [ Real.sqrt_nonneg 40, Real.sq_sqrt (show (0 : ℝ) ≤ 40 by positivity) ]
  linarith only [Real.pi_pos]
  nlinarith <;> rcases h₀ with ⟨next, _, _⟩
  nlinarith [(Real.neg_one_le_sin t), (Real.sin_sq_add_cos_sq t), (Real.cos_le_one t)]
  nth_rw 1 [h_S_sq_identity] <;> ring
  case _ =>
    linarith [ Real.sin_sq_add_cos_sq t]