import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_150
  (n : ℕ)
  (h₀ : ¬ Nat.Prime (7 + 30 * n)) :
  6 ≤ n := by

  rcases n with (_ | _ | _ | _ | _ | _ | nm) <;> norm_num [Nat.prime_def_lt] at * <;> omega