import Mathlib
open BigOperators Real Nat Topology

theorem amc12_2000_p12
  (a m c : ℕ)
  (h₀ : a + m + c = 12) :
  a*m*c + a*m + m*c + a*c ≤ 112 := by

  first
  | nlinarith
  | have h_le : a ≤ 12 := by linarith
    have h_le : m ≤ 12 := by linarith
    have h_le : c ≤ 12 := by linarith
    interval_cases a <;> interval_cases m <;> omega