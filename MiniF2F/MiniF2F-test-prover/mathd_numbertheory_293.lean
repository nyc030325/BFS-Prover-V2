import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_293
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 11∣20 * 100 + 10 * n + 7) :
  n = 5 := by

  interval_cases ms : n <;> norm_num1 at h₀ h₁ ⊢ <;>
    omega