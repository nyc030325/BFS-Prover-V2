import Mathlib
open BigOperators Real Nat Topology

theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by

  induction' h₁ <;> aesop
  rw [pow_succ] at *
  rw [← mul_one ((a ^ (m + 1) + b ^ (m + 1)) / 2)]
  ring_nf at a_ih ⊢
  nontriviality
  rcases le_total a b with h | h
  all_goals nlinarith [pow_le_pow_left (by linarith [left]) h m]