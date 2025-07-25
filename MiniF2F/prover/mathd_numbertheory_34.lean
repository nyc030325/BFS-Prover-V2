import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_34
  (x: ℕ)
  (h₀ : x < 100)
  (h₁ : x*9 % 100 = 1) :
  x = 89 := by

  all_goals interval_cases explicit: x <;> simp_all [Nat.mul_mod]