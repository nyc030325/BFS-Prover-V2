import Mathlib
open BigOperators Real Nat Topology

theorem aime_1994_p3
  (f : ℤ → ℤ)
  (h0 : ∀ x, f x + f (x-1) = x^2)
  (h1 : f 19 = 94):
  f (94) % 1000 = 561 := by

  have aux (n : ℤ) : f n = n ^ 2 - f (n - 1) := by linarith [h0 n]
  simp [h1, aux, eq_comm]