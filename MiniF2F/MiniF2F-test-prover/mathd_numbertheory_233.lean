import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_233
  (b :  ZMod (11^2))
  (h₀ : b = 24⁻¹) :
  b = 116 := by

  rw [h₀]            <;> norm_cast