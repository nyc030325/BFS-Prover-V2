import Mathlib
open BigOperators Real Nat Topology

theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by

  nlinarith [sq_nonneg (c - b), sq_nonneg (a - c), sq_nonneg (b - a),
    mul_nonneg (sub_nonneg.2 h₁.le) (sub_nonneg.2 h₂.le), mul_nonneg (sub_nonneg.2 h₂.le)
    (sub_nonneg.2 h₃.le), mul_nonneg (sub_nonneg.2 h₃.le) (sub_nonneg.2 h₁.le)]