import Mathlib
open BigOperators Real Nat Topology

theorem induction_12dvd4expnp1p20
  (n : ℕ) :
  12 ∣ 4^(n+1) + 20 := by

  induction' n with pn hpn <;> simp [pow_succ] <;> omega