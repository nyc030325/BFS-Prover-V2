import Mathlib
open BigOperators Real Nat Topology

theorem mathd_algebra_296 :
  abs (((3491 - 60) * (3491 + 60) - 3491^2):ℤ) = 3600 := by

  first
   | rfl
   | simp [add_comm]
       <;> ring