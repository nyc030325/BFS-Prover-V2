import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_765
  (x : ℤ)
  (h₀ : x < 0)
  (h₁ : (24 * x) % 1199 = 15) :
  x ≤ -449 := by

  obtain ⟨k, rfl⟩|⟨k, rfl⟩  := Int.even_or_odd x
    <;> ring_nf at *
    <;> omega