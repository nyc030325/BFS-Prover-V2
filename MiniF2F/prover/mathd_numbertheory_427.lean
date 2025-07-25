import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_427
  (a : ℕ)
  (h₀ : a = (∑ k in (Nat.divisors 500), k)) :
  ∑ k in Finset.filter (λ x => Nat.Prime x) (Nat.divisors a), k = 25 := by

  classical
    rw [h₀]
    native_decide