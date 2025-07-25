import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_321
  (n :  ZMod 1399)
  (h₁ : n = 160⁻¹) :
  n = 1058 := by

  rw[h₁] <;> native_decide