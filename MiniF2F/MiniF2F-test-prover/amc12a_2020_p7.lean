import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2020_p7
  (a : ℕ → ℕ)
  (h₀ : (a 0)^3 = 1)
  (h₁ : (a 1)^3 = 8)
  (h₂ : (a 2)^3 = 27)
  (h₃ : (a 3)^3 = 64)
  (h₄ : (a 4)^3 = 125)
  (h₅ : (a 5)^3 = 216)
  (h₆ : (a 6)^3 = 343) :
  ∑ k in Finset.range 7, (6 * (a k)^2) - ↑(2 * ∑ k in Finset.range 6, (a k)^2) = 658 := by

  norm_num [Finset.sum_range_succ, show a 0 = 1 by nlinarith [sq_nonneg (a 0), h₀],
    show a 1 = 2 by nlinarith [sq_nonneg (a 1), h₁], show a 2 = 3 by nlinarith [sq_nonneg (a 2), h₂],
    show a 3 = 4 by nlinarith [sq_nonneg (a 3), h₃], show a 4 = 5 by nlinarith [sq_nonneg (a 4), h₄],
    show a 5 = 6 by nlinarith [sq_nonneg (a 5), h₅], show a 6 = 7 by nlinarith [sq_nonneg (a 6), h₆]]