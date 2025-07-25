import Mathlib
open BigOperators Real Nat Topology

theorem induction_sumkexp3eqsumksq
  (n : ℕ) :
  ∑ k in Finset.range n, k^3 = (∑ k in Finset.range n, k)^2 := by

  induction' n with bn bih
  all_goals simp [Finset.sum_range_succ, *] <;>
   ring
  cases' bn with bn <;> simp [Finset.sum_range_succ, *] <;> ring
  clear bih
  induction' bn with bn ih <;> simp [Finset.sum_range_succ, *] at * <;> nlinarith