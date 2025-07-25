import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_239 :
  (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by

  next => norm_num[Finset.sum_Icc_succ_top]