import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_208 :
  Real.sqrt 1000000 - 1000000^((1 : ℝ)/3) = 900 := by

  simp [(show (1000000 : ℝ) = 1000 ^ 2 by norm_cast), Real.rpow_def_of_pos]
  field_simp [show (1000 : ℝ) = 10 ^ 3 by norm_cast] <;> ring_nf <;> norm_num
  rw [@sub_eq_iff_eq_add] <;>norm_num [Real.exp_mul,Real.exp_log]