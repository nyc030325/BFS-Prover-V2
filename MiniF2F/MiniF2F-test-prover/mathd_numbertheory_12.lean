import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_12 :
  Finset.card (Finset.filter (λ x => 20∣x) (Finset.Icc 15 85)) = 4 := by

  rcases lt_or_le 20 15 with h | h <;> native_decide <;> linarith