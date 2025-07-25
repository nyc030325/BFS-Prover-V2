import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_247
  (n : ℕ)
  (h₀ : (3 * n) % 11 = 2) :
  n % 11 = 8 := by

  classical
  all_goals
  repeat
       omega