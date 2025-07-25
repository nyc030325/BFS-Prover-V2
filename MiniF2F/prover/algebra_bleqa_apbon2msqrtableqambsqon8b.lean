import Mathlib
open BigOperators Real Nat Topology

theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by

  cases' h₀ with positivity
  exact
    (le_div_iff $ by positivity).mpr <|
      by nlinarith [Real.sq_sqrt (by positivity : 0 ≤ a * b), Real.sqrt_nonneg (a * b), sq_nonneg (a - b),
        sq_nonneg (a - 2 * √(a * b) + b)]