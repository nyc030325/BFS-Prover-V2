import Mathlib
open BigOperators Real Nat Topology

theorem amc12_2000_p6
  (p q : ℕ)
  (h₀ : Nat.Prime p ∧ Nat.Prime q)
  (h₁ : 4 ≤ p ∧ p ≤ 18)
  (h₂ : 4 ≤ q ∧ q ≤ 18) :
  p * q - (p + q) ≠ 194 := by

  rcases h₁ with ⟨hp1, hp2⟩ <;> rcases h₂ with ⟨hq1, hq2⟩ <;> interval_cases p <;> interval_cases q <;>. simp_all (config := {decide := true}) <;> nlinarith