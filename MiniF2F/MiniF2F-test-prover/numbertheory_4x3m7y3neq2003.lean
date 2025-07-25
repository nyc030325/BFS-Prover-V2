import Mathlib
open BigOperators Real Nat Topology

theorem numbertheory_4x3m7y3neq2003
  (x y : ℤ) :
  4 * x^3 - 7 * y^3 ≠ 2003 := by

  by_contra A
  rw [← Int.emod_add_ediv x 7, ← Int.emod_add_ediv y 7] at A
  ring_nf at A <;> have hx := Int.emod_nonneg x (by decide : (7 : ℤ) ≠ 0) <;>
              have hy := Int.emod_nonneg y (by decide : (7 : ℤ) ≠ 0) <;>
              have hx' := Int.emod_lt_of_pos x (by decide : (0 : ℤ) < 7) <;>
              have hy' := Int.emod_lt_of_pos y (by decide : (0 : ℤ) < 7) <;>
              interval_cases hx : x % (7 : ℤ) <;> interval_cases hy : y % (7 : ℤ) <;> omega