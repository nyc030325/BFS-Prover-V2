import Mathlib
open BigOperators Real Nat Topology

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by

  split_ands <;> try cases' abs_cases (x - 1) <;> try cases' abs_cases x <;> try cases' abs_cases (x + 1) <;> linarith