import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_235 :
  (29 * 79 + 31 * 81) % 10 = 2 := by

  simpa [Nat.add_mod, mul_mod]