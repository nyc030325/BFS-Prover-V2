import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_207 :
  8 * 9^2 + 5 * 9 + 2 = 695 := by

  conv_lhs => rewrite [add_comm] <;> norm_num1