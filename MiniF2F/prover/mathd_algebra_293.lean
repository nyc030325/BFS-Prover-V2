import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_293
  (x : NNReal) :
  Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := by

  rw [← sq_eq_sq (by positivity) (by positivity), mul_pow]
  simp [mul_pow] <;> ring <;> norm_num