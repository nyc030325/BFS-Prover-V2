import Mathlib
open BigOperators Real Nat Topology

theorem induction_prod1p1onk3le3m1onn
  (n : ℕ)
  (h₀ : 0 < n) :
  ∏ k in Finset.Icc 1 n, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / ↑n := by

  induction h₀ <;> simp_all [Finset.prod_Icc_succ_top]
  all_goals norm_num[Nat.one_le_of_lt]
  refine' (mul_le_mul_of_nonneg_right ‹_› <| by positivity).trans _
  field_simp [pow_succ, mul_add] at *
  · rw [div_le_div_iff (by positivity) (by positivity)]
    nlinarith