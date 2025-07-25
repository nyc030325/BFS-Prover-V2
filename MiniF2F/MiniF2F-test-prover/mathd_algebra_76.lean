import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_76
  (f : ℤ → ℤ)
  (h₀ : ∀n, Odd n → f n = n^2)
  (h₁ : ∀ n, Even n → f n = n^2 - 4*n -1) :
  f 4 = -1 := by

  norm_num [
    h₁ 4 (Int.even_iff.mpr (by decide)),
    h₀ 5 (show Odd 5 by decide)]