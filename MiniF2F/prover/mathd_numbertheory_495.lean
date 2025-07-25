import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_495
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a % 10 = 2)
  (h₂ : b % 10 = 4)
  (h₃ : Nat.gcd a b = 6) :
  108 ≤ Nat.lcm a b := by

  have hmul := Nat.gcd_mul_lcm a b
  by_contra hyp1
  have hdiv := Nat.gcd_dvd a b
  aesop (add simp Nat.dvd_iff_mod_eq_zero)
  obtain ⟨l, hl⟩ := Nat.dvd_of_mod_eq_zero left_1
  rcases b with (_ | _ | m) <;> simp_all
  on_goal 1 =>
     have : m + 1 + 1 < 108 :=
       by nlinarith
     have : m < 106 := by omega
     interval_cases m <;> simp_all (config := { decide := true })
  all_goals
     replace h₃ := h₃.symm
     have  : l < 10 := by
        nlinarith
     interval_cases l <;> norm_num at *