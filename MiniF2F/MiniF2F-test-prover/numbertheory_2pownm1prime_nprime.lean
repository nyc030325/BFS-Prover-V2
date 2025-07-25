import Mathlib
open BigOperators Real Nat Topology

theorem numbertheory_2pownm1prime_nprime
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Nat.Prime (2^n - 1)) :
  Nat.Prime n := by

  rcases n with _|_|n
  pick_goal 3
  any_goals simp at*
  all_goals have := h₁.two_le; aesop
  contrapose h₁
  simp [Nat.prime_def_lt] at h₁ ⊢
  refine' fun _ => _
  cases' h₁ with x hx_dvd
  refine ⟨2^x-1, ?_, ?_, ?_⟩
  rotate_left
  obtain ⟨_, h⟩ := hx_dvd.2.1
  any_goals aesop
  have := Nat.pow_mul (2 : ℕ) x w
  rotate_left
  obtain h | h := x <;> aesop
  any_goals rw [this] at *
  cases h <;> aesop (add simp pow_succ)
  have this : x ≤ n + 1 + 1
  apply Nat.le_of_dvd <;> aesop
  replace := Nat.pow_lt_pow_right (by norm_num : (1 : ℕ) < 2) left
  all_goals  ring_nf at *
  have : 2 ^ x ≤ 2 ^ n * 4 := by omega
  obtain _ | _ | x := x
  any_goals simp_all [Nat.pow_add, pow_mul] <;> try omega
  let a : ℕ := 2 ^ x
  let b : ℕ := a ^ w
  clear_value a b
  simpa using nat_sub_dvd_pow_sub_pow _ 1 w