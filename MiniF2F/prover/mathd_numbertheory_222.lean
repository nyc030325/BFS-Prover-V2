import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_222
  (b : ℕ)
  (h₀ : Nat.lcm 120 b = 3720)
  (h₁ : Nat.gcd 120 b = 8) :
  b = 248 := by

  have gcd_mul_lcm := Nat.gcd_mul_lcm 120 b <;> nlinarith