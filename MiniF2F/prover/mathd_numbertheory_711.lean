import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_711
  (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : Nat.gcd m n = 8)
  (h₂ : Nat.lcm m n = 112) :
  72 ≤ m + n := by

  have l0 := Nat.gcd_mul_lcm m n
  by_contra!
     <;> simp_all
  classical
  have  : m < 72 := by nlinarith
  interval_cases m <;> (try omega) <;> simp_all (config := {decide := true})
  all_goals
     have : n < 50 := by omega
     interval_cases n <;> simp_all (config := { decide := true})
       <;> try apply False.elim
                 <;> linarith