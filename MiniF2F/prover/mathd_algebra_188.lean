import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_188
  (σ : Equiv ℝ ℝ)
  (h : σ.1 2 = σ.2 2) :
  σ.1 (σ.1 2) = 2 := by

  convert σ.right_inv 2 using 2