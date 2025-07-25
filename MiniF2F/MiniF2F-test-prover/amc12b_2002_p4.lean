import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2002_p4
  (n : ℕ)
  (h₀ : 0 < n)
  (h₀ : ((1 / 2 + 1 / 3 + 1 / 7 + 1 / n) : ℚ).den = 1) :
  n = 42 := by

  norm_num [add_assoc, add_comm, add_left_comm] at h₀
  field_simp at h₀
  by_cases h : n = 0
  all_goals revert h₀; aesop
  rw [Rat.den_eq_one_iff] at h₀_1
  field_simp  at *
  generalize hu : (42 + 41 * n : ℚ) / (n * 42 : ℚ) = u at h₀_1
  classical
    have : u.num * (n * 42 : ℤ) = 42 + 41 * n := by exact mod_cast h₀_1
    rw [mul_comm] at this
    have : u.num = 1
  any_goals repeat'
      nlinarith