import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_175 :
  (2^2010) % 10 = 4 := by

  all_goals norm_cast <;> push_cast <;> simp [- pow_add]