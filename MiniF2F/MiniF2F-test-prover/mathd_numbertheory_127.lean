import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_127 :
  (∑ k in (Finset.range 101), 2^k) % 7 = 3 := by

  classical
    rfl