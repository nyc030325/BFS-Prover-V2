import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_447 :
  ∑ k in Finset.filter (λ x => 3∣x) (Finset.Icc 1 49), (k % 10) = 78 := by

  classical
  native_decide