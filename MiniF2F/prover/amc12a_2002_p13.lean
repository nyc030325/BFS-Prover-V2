import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2002_p13
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a ≠ b)
  (h₂ : abs (a - 1/a) = 1)
  (h₃ : abs (b - 1/b) = 1) :
  a + b = Real.sqrt 5 := by

  aesop (add simp [abs_eq, mul_comm])
  any_goals apply Eq.symm; rw [← sq_eq_sq (by positivity) (by positivity)]; field_simp at *; ring
  any_goals nlinarith [mul_pos (left) (right), mul_self_pos.2 <| sub_ne_zero.2 h₁]