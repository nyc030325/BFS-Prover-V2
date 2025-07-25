import Mathlib
open BigOperators Real Nat Topology

theorem mathd_numbertheory_341
  (a b c : ℕ)
  (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
  (h₁ : Nat.digits 10 ((5^100) % 1000) = [c,b,a]) :
  a + b + c = 13 := by

  norm_num [and_comm, and_left_comm] at h₀ <;> simp [h₀] at h₁ ⊢ <;>
     omega