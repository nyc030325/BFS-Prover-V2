import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2021_p14 :
  (∑ k in (Finset.Icc 1 20), (Real.logb (5^k) (3^(k^2)))) * (∑ k in (Finset.Icc 1 100), (Real.logb (9^k) (25^k))) = 21000 := by

  apply eq_of_beq <;> norm_num [logb, Finset.sum_range_succ, Finset.sum_Icc_succ_top]
  ring_nf <;> field_simp [show (25 : ℝ) = 5 ^ 2 by norm_cast, show (9 : ℝ) = 3 ^ 2 by norm_cast] <;>
    ring