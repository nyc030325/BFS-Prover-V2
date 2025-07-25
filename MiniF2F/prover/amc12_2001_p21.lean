import Mathlib
open BigOperators Real Nat Topology

theorem amc12_2001_p21
  (a b c d : ℕ)
  (h₀ : a * b * c * d = Nat.factorial 8)
  (h₁ : a * b + a + b = 524)
  (h₂ : b * c + b + c = 146)
  (h₃ : c * d + c + d = 104) :
  ↑a - ↑d = (10 : ℤ) := by

  norm_num [Nat.factorial_succ] at h₀
  on_goal 1 =>
    have h₄ : c ≤ 146 := by nlinarith
    interval_cases c <;> try omega
  any_goals try
    have hd : d ≤ 104 := by omega
    interval_cases d <;> try omega