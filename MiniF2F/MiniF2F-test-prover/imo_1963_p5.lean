import Mathlib
open BigOperators Real Nat Topology

theorem imo_1963_p5 :
  Real.cos (π / 7) - Real.cos (2 * π / 7) + Real.cos (3 * π / 7) = 1 / 2 := by

  have x : Real.pi / 7 = Real.pi / 7 * 1 := by ring
  have h : 3 * Real.pi / 7 = Real.pi - 4 * Real.pi / 7 := by ring
  rw [h, cos_sub] <;> norm_num
  have h2 := cos_two_mul (Real.pi / 7)
  have h3 := cos_three_mul (π / 7)
  rw [show 4 * Real.pi / 7 = Real.pi - 3 * Real.pi / 7 by ring,
    cos_sub]
  simp [h2, h3, cos_two_mul, sin_pi, cos_pi]
  ring_nf at h2 h3 ⊢
  norm_num [h2, h3, cos_pi_div_two]
  ring_nf
    <;> have h4 := cos_pi
    <;> simp [h4]
  ring_nf at * <;> norm_num
  rw [← sub_eq_zero]
  nth_rewrite 1 [← sub_eq_zero]
  ring_nf
  apply eq_of_sub_eq_zero
  let y := cos (Real.pi * (1 / 7))
  have:= cos_three_mul (Real.pi * (1 / 7))
  ring_nf at *
  apply eq_of_sub_eq_zero
  clear this h3 h2
  apply eq_of_sub_eq_zero
  have := cos_three_mul (Real.pi * (1 / 7))
  field_simp [mul_assoc] at *
  on_goal 1 => ring
  replace : Real.pi * (1 / 7 : ℝ) = Real.pi / 7 := by ring
  try rw [this]; norm_num
  have h5 := cos_three_mul (Real.pi / 7)
  have : 3 * (Real.pi / 7) = Real.pi - 4 * (Real.pi / 7) := by ring
  simp [this, cos_pi] at h5
  let z := cos (Real.pi / 7)
  rcases lt_trichotomy 0 z with hz | hz | hz
  any_goals simp_all [show cos (4 * (Real.pi / 7)) = cos (2 * (2 * (Real.pi / 7))) by ring,
   cos_two_mul]
  any_goals nlinarith [cos_sq_add_sin_sq (Real.pi / 7), Real.sin_pi_div_two_sub, pow_two_nonneg (cos (Real.pi / 7) - 1),pow_two_nonneg (cos (Real.pi / 7) + 1)]
  contrapose hz
  refine not_lt.2 ?_
  apply cos_nonneg_of_mem_Icc <;> constructor <;> linarith [pi_pos]