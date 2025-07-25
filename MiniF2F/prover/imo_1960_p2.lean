import Mathlib
open BigOperators Real Nat Topology

theorem imo_1960_p2
  (x : ℝ)
  (h₀ : 0 ≤ 1 + 2 * x)
  (h₁ : (1 - Real.sqrt (1 + 2 * x))^2 ≠ 0)
  (h₂ : (4 * x^2) / (1 - Real.sqrt (1 + 2*x))^2 < 2*x + 9) :
  -(1 / 2) ≤ x ∧ x < 45 / 8 := by

  constructor <;> contrapose! h₂
  all_goals rw [le_div_iff' (by positivity)]; nlinarith [mul_self_nonneg (2 * x + 3 - √(1 + 2 * x)),
   Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * x), Real.sqrt_pos.2 (by linarith : (0 : ℝ) < 1 + 2 * x)]