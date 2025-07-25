import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2002_p6
  (n : ℕ)
  (h₀ : 0 < n) :
  ∃ m, (m > n ∧ ∃ p, m * p ≤ m + p) := by

  exact ⟨n+1, by omega, 1, by omega⟩