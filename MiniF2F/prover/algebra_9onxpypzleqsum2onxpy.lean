import Mathlib
open BigOperators Real Nat Topology

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by

  obtain ⟨hx, hy, hz⟩ := h₀ <;> field_simp
  apply (div_le_div_iff (by positivity) (by positivity)).mpr <;> nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]