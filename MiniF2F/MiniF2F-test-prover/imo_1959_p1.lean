import Mathlib
open BigOperators Real Nat Topology

theorem imo_1959_p1
  (n : ℕ)
  (h₀ : 0 < n) :
  Nat.gcd (21*n + 4) (14*n + 3) = 1 := by

  simp [(show 21 * n + 4 = (14 * n + 3) + (7 * n + 1) by ring), (show 14 * n + 3 = 2 * (7 * n + 1) + 1 by ring)]