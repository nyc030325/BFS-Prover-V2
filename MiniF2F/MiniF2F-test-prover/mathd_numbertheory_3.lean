import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_3 :
  (∑ x in Finset.range 10, ((x + 1)^2)) % 10 = 5 := by

  apply (show ((0 + 1) ^ 2 + (1 + 1) ^ 2 + (2 + 1) ^ 2 + (3 + 1) ^ 2
  + (4 + 1) ^ 2 + (5 + 1) ^ 2 + (6 + 1) ^ 2 + (7 + 1) ^ 2
  + (8 + 1) ^ 2) % 10 = 5 by rfl)