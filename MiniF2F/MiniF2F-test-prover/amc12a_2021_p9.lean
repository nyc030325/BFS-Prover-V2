import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2021_p9 :
  ∏ k in Finset.range 7, (2^(2^k) + 3^(2^k)) = 3^128 - 2^128 := by

  norm_num [Finset.prod_range_succ, Finset.range_zero]