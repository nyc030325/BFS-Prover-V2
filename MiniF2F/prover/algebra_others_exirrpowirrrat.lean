import Mathlib
open BigOperators Real Nat Topology

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by

  let a  := Real.sqrt 2
  by_cases c:Irrational (a^a)
  use a^a, a
  repeat' first
  | constructor
  | assumption
  repeat' apply irrational_sqrt_two
  rw [← Real.rpow_mul (le_of_lt (Real.sqrt_pos.2 zero_lt_two))]
  aesop