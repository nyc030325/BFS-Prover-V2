import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_184
  (a b : NNReal)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : (a^2) = 6*b)
  (h₂ : (a^2) = 54/b) :
  a = 3 * NNReal.sqrt 2 := by

  obtain ⟨ _, _⟩ := h₀
  simp_all [← NNReal.coe_inj]
  rw [mul_comm, ← sq_eq_sq (by positivity) (by positivity)] <;> ring
  field_simp at * <;> nlinarith