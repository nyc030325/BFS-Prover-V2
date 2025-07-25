import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_237 :
  (∑ k in (Finset.range 101), k) % 6 = 4 := by

  simp [Finset.sum_range_id, Int.add, Int.mul]