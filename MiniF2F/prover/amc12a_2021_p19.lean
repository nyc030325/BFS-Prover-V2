import Mathlib
open BigOperators Real Nat Topology

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem amc12a_2021_p19
  (S : Finset ℝ)
  (h₀ : ∀ (x : ℝ), x ∈ S ↔ 0 ≤ x ∧ x ≤ Real.pi ∧ Real.sin (Real.pi / 2 * Real.cos x) = Real.cos (Real.pi / 2 * Real.sin x)) :
  S.card = 2 := by

  try convert_to _ = (({0, 1} : Finset ℝ).image fun x => x).card
  all_goals norm_num [ Finset.image]
  have  : S = {0, Real.pi / 2}
  symm <;> rw [Finset.ext_iff] <;> aesop
  repeat' linarith [Real.pi_pos, Real.pi_nonneg]
  on_goal 2 => simp [*]
  rw [or_iff_not_imp_right]
  rintro h₃
  apply le_antisymm
  any_goals
    aesop
  on_goal 1 => contrapose h₃
  all_goals norm_num [pi_ne_zero]
  rcases eq_or_lt_of_le left_1 with (rfl | h₁)
  any_goals intros; norm_num at *
  apply le_antisymm <;> contrapose right
  rotate_left 1
  on_goal 2 => rw [Finset.card_insert_of_not_mem]
  any_goals apply_fun Real.arcsin
  any_goals erw [← Real.sin_pi_div_two_sub]
  any_goals specialize h₀ 0; simp_all
  any_goals aesop (add simp [Real.sin_pi_div_two_sub])
  rw [mul_comm] at a_1
  any_goals rw [eq_comm] at *
  any_goals
    first | nlinarith | have h₁ := h₀
  any_goals field_simp [Real.pi_ne_zero] at * <;> (try linarith)
  all_goals rw [← Real.sin_pi_div_two_sub] at a_1; norm_num at a_1
  all_goals rw [Real.arcsin_sin, Real.arcsin_sin] at a_1
  repeat' nlinarith [sin_pos_of_pos_of_lt_pi h₃ (by linarith), sin_le_one a, cos_nonneg_of_mem_Icc ⟨by linarith, right.le⟩]
  any_goals
    contrapose h₁
    aesop
  any_goals nlinarith [Real.pi_pos, sin_pos_of_pos_of_lt_pi h₃ h₁_1, cos_neg_of_pi_div_two_lt_of_lt right (by linarith), cos_sq_add_sin_sq a]
  any_goals
       nlinarith [ Real.sin_pos_of_pos_of_lt_pi h₃ (by linarith), Real.cos_le_one a, Real.pi_pos]
  contrapose! h₀
  refine Or.inr ⟨?_, ?_⟩ <;> try first | positivity | linarith [pi_pos]
  have h₁  : 0 < sin a := sin_pos_of_pos_of_lt_pi h₃ h₁_1
  by_contra hh
  contrapose h₃ <;> aesop
  contrapose h₁_1
  first |nlinarith|rw [not_lt]
  absurd h₁_1
  contrapose! a_1
  rw [← sub_ne_zero]
  have h₂ : 0 < cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith, right⟩
  refine (sub_ne_zero.mpr ?_)
  nlinarith [pi_pos, mul_pos h₂ h₁,
    Real.sin_sq_add_cos_sq a, sin_le_one a, cos_le_one a]