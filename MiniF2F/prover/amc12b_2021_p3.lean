import Mathlib
open BigOperators Real Nat Topology

theorem amc12b_2021_p3
  (x : ℝ)
  (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) :
  x = 3 / 4 := by

  rcases eq_or_ne (3 + x) 0 with hr | hr <;> rcases eq_or_ne (2 + 2 / (3 + x)) 0 with hr₂ | hr₂ <;>
    rcases eq_or_ne (1 + 1 / (2 + 2 / (3 + x))) 0 with hr₃ | hr₃ <;> field_simp [hr, hr₂, hr₃] at * <;> try linarith
  all_goals field_simp [hr₂] at h₀ hr₃
  any_goals field_simp [hr₃] at h₀; linarith