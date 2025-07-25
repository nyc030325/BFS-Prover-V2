import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_398
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 9 * b = 20 * c)
  (h₂ : 7 * a = 4 * b) :
  63 * a = 80 * c := by

  nlinarith [Eq.symm h₁, Eq.symm h₂, add_pos h₀.1 h₀.2.1 ]