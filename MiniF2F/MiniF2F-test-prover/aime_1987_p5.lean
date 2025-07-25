import Mathlib
open BigOperators Real Nat Topology

theorem aime_1987_p5
  (x y : ℤ)
  (h₀ : y^2 + 3 * (x^2 * y^2) = 30 * x^2 + 517):
  3 * (x^2 * y^2) = 588 := by

  on_goal 1 =>
    have : y ^ 2 ≤ 30 * x ^ 2 + 517 := by nlinarith
    have : y ^ 2 < 600 := by nlinarith
    have : y ≤ 24 := by nlinarith
    have : y ≥ -24 := by nlinarith
    interval_cases y<;> try (omega)