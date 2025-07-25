import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_541
  (m n : ℕ)
  (h₀ : 1 < m)
  (h₁ : 1 < n)
  (h₂ : m * n = 2005) :
  m + n = 406 := by

  if hm : m > 41 then
  have : n < 50 := by nlinarith
  interval_cases n <;> omega
  else 
  interval_cases m <;> omega