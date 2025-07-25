import Mathlib
open BigOperators Real Nat Topology

theorem aime_1997_p9
  (a : ℝ)
  (h₀ : 0 < a)
  (h₁ : 1 / a - Int.floor (1 / a) = a^2 - Int.floor (a^2))
  (h₂ : 2 < a^2)
  (h₃ : a^2 < 3) :
  a^12 - 144 * (1 / a) = 233 := by

  simp [sub_eq_iff_eq_add, add_assoc] at h₁
  any_goals rw [Int.fract_eq_fract] at h₁
  obtain ⟨z, hyp⟩ := h₁
  rcases z with (_ | _ | m)
  all_goals field_simp at *
  any_goals norm_cast at * ; nlinarith [pow_pos h₀ 12, pow_pos h₀, pow_pos h₀ 2, pow_pos h₀ 3, pow_pos h₀ 4, pow_pos h₀ 5, pow_pos h₀ 6, pow_pos h₀ 8, pow_pos h₀ 9]
  ring_nf at *
  rcases m with _|_|m
  all_goals norm_num  at *
  repeat' nlinarith [pow_pos h₀ 2, pow_pos h₀ 3, pow_pos h₀ 4, pow_pos h₀ 5, pow_pos h₀ 6, pow_pos h₀ 7,
    pow_pos h₀ 8, pow_pos h₀ 9, pow_pos h₀ 10, pow_pos h₀ 11, pow_pos h₀ 12]