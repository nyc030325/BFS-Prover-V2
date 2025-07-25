import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_559
  (x y : ℕ)
  (h₀ : x % 3 = 2)
  (h₁ : y % 5 = 4)
  (h₂ : x % 10 = y % 10) :
  14 ≤ x := by

  first
  | omega
  | apply @Nat.le_of_not_lt