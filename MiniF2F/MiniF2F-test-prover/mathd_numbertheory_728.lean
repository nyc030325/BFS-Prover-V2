import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_728 :
  (29^13 - 5^13) % 7 = 3 := by

  dsimp [ Nat.pow] <;> norm_num