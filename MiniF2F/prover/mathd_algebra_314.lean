import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_314
  (n : ℕ)
  (h₀ : n = 11) :
  (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4 := by

  norm_num [two_mul, h₀]