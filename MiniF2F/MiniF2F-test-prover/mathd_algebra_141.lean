import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_141
  (a b : ℝ)
  (h₁ : (a * b)=180)
  (h₂ : 2 * (a + b)=54) :
  (a^2 + b^2) = 369 :=
  by sorry

theorem mathd_numbertheory_3 :
  (∑ x in Finset.range 10, ((x + 1)^2)) % 10 = 5 := by

  repeat' nlinarith [two_mul (a + b), h₁]