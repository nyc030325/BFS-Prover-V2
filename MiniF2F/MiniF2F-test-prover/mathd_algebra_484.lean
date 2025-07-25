import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_484 :
  Real.log 27 / Real.log 3 = 3 := by

  field_simp [show (27 :ℝ) = 3 ^ 3 by norm_cast, show (3 :ℝ) ≠ 1 by norm_num]