import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_343 :
  (∏ k in Finset.range 6, (2 * k + 1)) % 10 = 5 := by

  rfl 
  <;>  rfl