import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_430
  (a b c : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9)
  (h₁ : 1 ≤ b ∧ b ≤ 9)
  (h₂ : 1 ≤ c ∧ c ≤ 9)
  (h₃ : a ≠ b)
  (h₄ : a ≠ c)
  (h₅ : b ≠ c)
  (h₆ : a + b = c)
  (h₇ : 10 * a + a - b = 2 * c)
  (h₈ : c * b = 10 * a + a + a) :
  a + b + c = 8 := by

  all_goals
      have                 : c < 10 := by linarith
      interval_cases c <;>omega