import Mathlib
open BigOperators Real Nat Topology

theorem induction_11div10tonmn1ton
  (n : ℕ) :
  11 ∣ (10^n - (-1 : ℤ)^n) := by

  induction n using Nat.twoStepInduction <;> simp [_root_.pow_succ, Int.mul_emod, Int.emod_emod] <;> omega