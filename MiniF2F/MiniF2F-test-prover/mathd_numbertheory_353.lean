import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_353
  (s : ℕ)
  (h₀ : s = ∑ k in Finset.Icc 2010 4018, k) :
  s % 2009 = 0 := by

  rw[h₀] <;> repeat erw [Finset.sum_eq_multiset_sum] <;> native_decide