import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_362
  (a b : ℝ)
  (h₀ : a^2 * b^3 = 32 / 27)
  (h₁ : a / b^3 = 27 / 4) :
  a + b = 8 / 3 := by

  cases' eq_or_ne b 0 with hb hb  <;> aesop
  any_goals field_simp at h₀ h₁ ⊢
  rcases lt_or_gt_of_ne hb with hb | hb
  all_goals nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg b) (sq_nonneg (b ^ 2 - 4/9)), pow_two_nonneg (a - 3 * b)]