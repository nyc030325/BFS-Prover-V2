import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_345 :
  (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by

  conv => lhs; rw [add_assoc]; simp [add_comm, add_left_comm]