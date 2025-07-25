import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1)
  (h₄ : a ≠ c) :
  Real.sqrt ((a - c)^2 + (b - d)^2)= Real.sqrt 10 := by

  field_simp [@eq_comm ℝ]
  classical
  have : a = 1 - b := by linarith
  have : c = 1 - d := by linarith
  subst_vars
  nlinarith [mul_self_pos.mpr (sub_ne_zero.2 (Ne.symm h₄))]