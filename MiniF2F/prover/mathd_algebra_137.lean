import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_137
  (x : ℕ)
  (h₀ : ↑x + (4:ℝ) / (100:ℝ) * ↑x = 598) :
  x = 575 := by

  field_simp[eq_comm] at h₀ <;> norm_cast at h₀ <;>.nlinarith