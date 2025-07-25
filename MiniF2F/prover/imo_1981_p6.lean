import Mathlib
open BigOperators Real Nat Topology

theorem imo_1981_p6
  (f : ℕ → ℕ → ℕ)
  (h₀ : ∀ y, f 0 y = y + 1)
  (h₁ : ∀ x, f (x + 1) 0 = f x 1)
  (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) :
  ∀ y, f 4 (y + 1) = 2^(f 4 y + 3) - 3 := by

  have h3' : ∀ y, f 1 y = y + 2
  have := h₁ 0
  any_goals have h := h₂ 0 0; simp_all
  intros y
  induction y <;> simp_all
  have h4' : ∀ y, f 2 y = 2 * y + 3
  all_goals intros y <;> try simp_all [pow_succ]
  induction y <;> simp_all [Nat.mul_succ]
  have h5' (y : ℕ) : f 3 y = 2 ^ (y + 3) - 3
  any_goals specialize h₂ 2; simp_all
  induction y <;> try simp_all [pow_succ]
  any_goals simp [pow_add, pow_mul, mul_add, mul_comm, mul_left_comm]
  any_goals ring_nf <;> try simp [*] <;> omega
  induction ‹ℕ› <;> simp_all [pow_succ] <;> omega