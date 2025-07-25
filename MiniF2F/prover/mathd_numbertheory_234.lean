import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_234
  (a b : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
  (h₁ : (10 * a + b)^3 = 912673) :
  a + b = 16 := by

  on_goal 1 =>
    have ha : a ≤ 9 := h₀.2.1
    have h₁' : (10 * a + b) ^ 3 ≤ (10 * 9 + 9) ^ 3 := by nlinarith
    have h₂ : b ≤ 9 := h₀.2.2
    have : a + b ≤ 18 := by linarith
    interval_cases X : a <;> interval_cases Y : b <;> aesop