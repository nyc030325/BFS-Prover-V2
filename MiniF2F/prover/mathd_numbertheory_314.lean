import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_314
  (r n : ℕ)
  (h₀ : r = 1342 % 13)
  (h₁ : 0 < n)
  (h₂ : 1342∣n)
  (h₃ : n % 13 < r) :
  6710 ≤ n := by

  obtain _ | _ | n := h₂ <;> rcases n with (_ | _ | _ ) <;> omega