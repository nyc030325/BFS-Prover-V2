import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_299 :
  (1 * 3 * 5 * 7 * 9 * 11 * 13) % 10 = 5 := by

  solve|simp|apply eq_of_beq