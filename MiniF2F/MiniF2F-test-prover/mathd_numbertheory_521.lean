import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_521
  (m n : ℕ)
  (h₀ : Even m)
  (h₁ : Even n)
  (h₂ : m - n = 2)
  (h₃ : m * n = 288) :
  m = 18 := by

  classical 
    have : n ≤ m := by omega
    have : n < 30 := by nlinarith
    interval_cases n <;> omega