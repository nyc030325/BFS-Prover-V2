import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_457
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 80325∣(n !)) :
  17 ≤ n := by

  classical 
  by_contra hc; interval_cases n <;> norm_cast