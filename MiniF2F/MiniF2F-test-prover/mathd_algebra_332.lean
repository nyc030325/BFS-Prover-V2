import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_332
  (x y : ℝ)
  (h₀ : (x + y) / 2 = 7)
  (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
  x^2 + y^2 = 158 := by

  rw [@Real.sqrt, @Real.sqrt] at h₁ <;> norm_num at *
  try cases' max_eq_iff.1 h₁ with H H <;> try nlinarith