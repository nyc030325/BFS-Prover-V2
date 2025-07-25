import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_392
  (n : ℕ)
  (h₀ : Even n)
  (h₁ : ((n:ℤ) - 2)^2 + (n:ℤ)^2 + ((n:ℤ) + 2)^2 = 12296) :
  ((n - 2) * n * (n + 2)) / 8 = 32736 := by

  case _ =>
    have h₂ : n ≤ 111 := by nlinarith
    interval_cases n <;> norm_num at h₀ h₁ ⊢