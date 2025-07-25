import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_313
  (v i z : ℂ)
  (h₀ : v = i * z)
  (h₁ : v = 1 + Complex.I)
  (h₂ : z = 2 - Complex.I) :
  i = 1/5 + 3/5 * Complex.I := by

  field_simp [Complex.ext_iff, h₂, h₁] at * <;> ring <;> constructor <;> repeat' linarith