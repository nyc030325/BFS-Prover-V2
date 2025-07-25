import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_185
  (n : ℕ)
  (h₀ : n % 5 = 3) :
  (2 * n) % 5 = 1 := by

  simp [Nat.mul_mod, ← mod_mod_of_dvd, h₀]