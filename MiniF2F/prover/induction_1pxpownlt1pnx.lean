import Mathlib
open BigOperators Real Nat Topology

theorem induction_1pxpownlt1pnx
  (x : ℝ)
  (n : ℕ)
  (h₀ : -1 < x)
  (h₁ : 0 < n) :
  (1 + ↑n*x) ≤ (1 + x)^(n:ℕ) := by

  induction' h₁ <;> simp [*, pow_succ]
  nlinarith [pow_pos (show (0:ℝ) < 1 + x by linarith) ‹_›,
    sq_nonneg (x), le_of_lt h₀]