import Mathlib
open BigOperators Real Nat Topology

theorem induction_nfactltnexpnm1ngt3
  (n : ℕ)
  (h₀ : 3 ≤ n) :
  n ! < n^(n - 1) := by

  induction' h₀ with nn n_ih
  all_goals simp [factorial, pow_two, pow_succ]
  cases nn <;> simp_all [Nat.pow_succ, Nat.mul_comm]
  any_goals
  calc _ < (_:ℕ) ^ _ := by assumption
       _ ≤ (_:ℕ) ^ _ := by gcongr; simp_all