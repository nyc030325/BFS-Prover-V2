import Mathlib
open BigOperators Real Nat Topology

theorem numbertheory_notEquiv2i2jasqbsqdiv8 :
  ¬ (∀ a b : ℤ, (∃ i j, a = 2*i ∧ b=2*j) ↔ (∃ k, a^2 + b^2 = 8*k)) := by

  by_contra u
  have := u (2 * 1) (2 * 0) <;> simp at * <;> ring_nf at * <;> omega