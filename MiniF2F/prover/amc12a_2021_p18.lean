import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2021_p18
  (f : ℚ → ℝ)
  (h₀ : ∀x>0, ∀y>0, f (x * y) = f x + f y)
  (h₁ : ∀p, Nat.Prime p → f p = p) :
  f (25 / 11) < 0 := by

  have div := h₀ (5 : ℚ) (by norm_num) (5 : ℚ) (by norm_num)
  have prim := h₁ 5
  have help₁ := h₀ (5 : ℚ) (by norm_num) (5 : ℚ) (by norm_num)
  replace h₀ := h₀ (25 / 11) (by positivity) 11 (by norm_num)
  have help₂ := h₁ 11 (by decide)
  ring_nf at * <;>
  linarith [prim Nat.prime_five] <;> positivity