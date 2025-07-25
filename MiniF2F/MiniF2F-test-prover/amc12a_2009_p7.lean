import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2009_p7
  (x : ℝ)
  (n : ℕ)
  (a : ℕ → ℝ)
  (h₁ : ∀ m, a (m + 1) - a m = a (m + 2) - a (m + 1))
  (h₂ : a 1 = 2 * x - 3)
  (h₃ : a 2 = 5 * x - 11)
  (h₄ : a 3 = 3 * x + 1)
  (h₅ : a n = 2009) :
  n = 502 := by

  have : ∀ k, a k = 2 * x - 3 + (k - 1) * ((5 * x - 11) - (2 * x - 3))
  rintro k <;> induction k using Nat.twoStepInduction
  any_goals simp [*] at * <;> try linarith [h₁ 0]
  try linarith [h₁ ‹_›]
  refine Nat.cast_injective (by nlinarith : (n : ℝ) = 502)