import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_517 :
  (121 * 122 * 123) % 4 = 2 := by

  simp[mul_add, mul_comm, mul_assoc, mul_left_comm]