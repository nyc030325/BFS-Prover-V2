import Mathlib
open BigOperators Real Nat Topology

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem aime_1983_p3
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (x^2 + (18 * x +  30) - 2 * Real.sqrt (x^2 + (18 * x + 45))))
  (h₁ : Fintype (f⁻¹' {0})) :
  ∏ x in (f⁻¹' {0}).toFinset, x = 20 := by

  set s := (f ⁻¹' {0}).toFinset
  try rw [Finset.prod_eq_multiset_prod]
  erw [Set.preimage] at h₁
  simp only [Multiset.map_id', Set.mem_singleton_iff, Finset.prod_val, Finset.prod_map]
  have hs  : s = {(-9 + Real.sqrt 61), (-9 - Real.sqrt 61)}
  on_goal -1 => rw [hs]
  on_goal 1 => ext x
  any_goals aesop (add simp [Finset.prod])
  rw [or_iff_not_imp_right]
  any_goals field_simp [sub_eq_add_neg]
  aesop (add simp [sq])
  any_goals repeat' nlinarith [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 61)]
  any_goals ring_nf; norm_num
  cases' lt_or_gt_of_ne a_1 with h h
  any_goals
    rw [show Real.sqrt 25 = Real.sqrt (5 * 5) by norm_num, Real.sqrt_mul_self] <;> norm_num
  all_goals apply eq_of_sub_eq_zero
  all_goals ring_nf at *
  all_goals apply mul_right_cancel₀ (sub_ne_zero_of_ne a_1)
  all_goals ring!
  all_goals rw [ Real.sqrt] at *
  all_goals aesop (add simp [Real.sq_sqrt])
  all_goals cases' lt_or_le 0 (45 + x * 18 + x ^ 2) with hh hh
  any_goals field_simp [max_def, sq, h₀] at a
  repeat'
    split_ifs at a
    nlinarith [Real.sqrt_nonneg <| 45 + x * 18 + x ^ 2,Real.sq_sqrt (show (45 + x * 18 + x ^ 2 : ℝ) ≥ 0 by nlinarith )]
  any_goals norm_num at*
  any_goals aesop (add simp Real.sqrt_eq_zero_of_nonpos)
  all_goals nlinarith [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ 45 + x * 18 + x * x), Real.sqrt_nonneg (45 + x * 18 + x * x)]