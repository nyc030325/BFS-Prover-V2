import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_342 :
  54 % 6 = 0 := by

  norm_num [PNat.dvd_iff]