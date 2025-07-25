import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_320
  (n : ℕ)
  (h₀ : n < 101)
  (h₁ : 101 ∣ (123456 - n)) :
  n = 34 := by

  interval_cases xm : n <;> norm_num at * <;>.omega