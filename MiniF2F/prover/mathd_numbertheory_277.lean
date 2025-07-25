import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_277
  (m n : ℕ)
  (h₀ : Nat.gcd m n = 6)
  (h₁ : Nat.lcm m n = 126) :
  60 ≤ m + n := by

  contrapose! h₀
  have     := Nat.dvd_lcm_left m n
  any_goals
    have : n ∣ m.lcm n := Nat.dvd_lcm_right m n
    rw [h₁] at this
    have : n < 127 := by omega
    interval_cases n <;> repeat'
      omega
  any_goals
    have : m < 60 := by omega
    interval_cases m <;> simp_all (config := {decide := true})