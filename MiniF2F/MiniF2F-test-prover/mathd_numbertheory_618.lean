import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_618
  (n : ℕ)
  (hn : n > 0)
  (p : ℕ → ℕ)
  (h₀ : ∀ x, p x = x^2 - x + 41)
  (h₁ : 1 < Nat.gcd (p n) (p (n+1))) :
  41 ≤ n := by

  contrapose! h₁ with h
  interval_cases g : n <;> simp_all (config := { decide := true }) [h₀]