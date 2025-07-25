import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_296
  (n : ℕ)
  (h₀ : 2 ≤ n)
  (h₁ : ∃ x, x^3 = n)
  (h₂ : ∃ t, t^4 = n) :
  4096 ≤ n := by

  contrapose! h₂ <;> aesop
  on_goal 1 =>
    have : w < 16 :=
      by nlinarith [sq_nonneg (w^2)]
    interval_cases w <;> simp_all (config := {decide := true})
  any_goals 
    have btc : t < 16 := by nlinarith [pow_nonneg t.zero_le 2, pow_nonneg t.zero_le 3]
    interval_cases t <;>simp_all (config := {decide :=true})