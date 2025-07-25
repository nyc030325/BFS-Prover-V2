import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_158
  (a : ℕ)
  (h₀ : Even a)
  (h₁ : ∑ k in Finset.range 8, (2 * k + 1) - ∑ k in Finset.range 5, (a + 2 * k) = (4:ℤ)) :
  a = 8 := by

  norm_num [Finset.sum_range_succ', Finset.sum_range_zero] at h₁
    <;> ring_nf at h₁ ⊢
    <;> cases h₀
    <;> omega