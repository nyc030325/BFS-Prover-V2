import Mathlib
open BigOperators Real Nat Topology

theorem imo_1962_p2
  (x : ℝ)
  (h₀ : 0 ≤ 3 - x)
  (h₁ : 0 ≤ x + 1)
  (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) :
  -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by

  constructor <;> contrapose h₂ <;> try norm_num
  any_goals
    rw [Real.sqrt_le_left]
    norm_num
  all_goals nlinarith [Real.sqrt_nonneg (x+1), Real.mul_self_sqrt (by linarith : 0 ≤ x+1), Real.sqrt_nonneg (31:ℝ), Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 31)]