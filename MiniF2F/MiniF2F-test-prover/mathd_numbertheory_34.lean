import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_345 :
  (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by

  all_goals interval_cases explicit: x <;> simp_all [Nat.mul_mod]