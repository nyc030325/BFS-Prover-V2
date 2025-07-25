import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_769 :
  (129^34 + 96^38) % 11 = 9 := by

  simpa [pow_succ, Int.add_emod, Int.mul_emod] using (by decide : (129 : ℤ) % 11 = -2)