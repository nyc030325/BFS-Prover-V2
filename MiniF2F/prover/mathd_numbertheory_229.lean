import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_229 :
  (5^30) % 7 = 1 := by

  norm_num[show (5: Nat) ^ 30 % 7 = ((5 ^ 2) ^ 15 : Nat) % 7 by ring, pow_succ]