import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_328 :
  (5^999999) % 7 = 6 := by

  apply Eq.trans <;> ring_nf <;> rfl