import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_100
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Nat.gcd n 40 = 10)
  (h₂ : Nat.lcm n 40 = 280) :
  n = 70 := by

  all_goals      have h := Nat.gcd_mul_lcm n 40; simp_all; omega