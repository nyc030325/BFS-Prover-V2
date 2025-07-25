import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_125
  (x y : ℕ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : 5 * x = y)
  (h₂ : (↑x - (3:ℤ)) + (y - (3:ℤ)) = 30) :
  x = 6 := by

  exact mod_cast ((eq_comm.mp (by linarith)) : x = 6)