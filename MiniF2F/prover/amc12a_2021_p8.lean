import Mathlib
open BigOperators Real Nat Topology

theorem amc12a_2021_p8
  (d : ℕ → ℕ)
  (h₀ : d 0 = 0)
  (h₁ : d 1 = 0)
  (h₂ : d 2 = 1)
  (h₃ : ∀ n≥3, d n = d (n - 1) + d (n - 3)) :
  Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by

  have H₁ := h₁
  contrapose h₀
  push_neg  at h₀ ⊢
  any_goals contrapose h₀
  simp [not_forall] at h₀
  have h₁ := h₁
  erw [Nat.even_iff, Nat.odd_iff]
  have h₂' := h₃ 3 (by omega)
  all_goals norm_num at *
  set a : ℕ → ℕ := fun n => d n % 2
  have hacar : ∀ n, a (n + 7) = a n
  have h₂'' := h₃ 4 (by omega)
  all_goals have h₄ := h₃ 5 (by decide)
  any_goals try simp_all
  rotate_left
  on_goal 1 => have h₅ := h₃ 6 (by norm_cast)
  have h₇ := h₃ 7
  any_goals simp_arith [@Nat.even_iff]
  nth_rw 1 [show (2021 : ℕ) = 5 + 7 * 288 by calc
    (2021 : ℕ) = 7 * 288 + 5 := by omega
    _ = 5 + 7 * 288 := by ring]
  norm_num at *
  have hltr := h₃ 4 (by decide)
  norm_num  at hltr
  contrapose! hltr
  by_contra hip
  rw [h₁] at hip
  any_goals aesop?
  all_goals try simp [add_comm]
  any_goals repeat' specialize h₃ 3; simp_all
  any_goals revert h₅
  rw [← Nat.mod_add_div (d 6) 2]
  rotate_right 1
  cases hh : d n <;> cases hhh : d n <;> cases hhh : d n <;> omega
  have hterm := hacar 6
  revert d
  simp [-forall_const]
  intro d1 d2 d0 h0 h1 h2 h3
  have h4 := h1 0
  any_goals zify at * <;> try omega
  aesop (add simp [add_comm])
  cases' h6 : (d1 6)
  any_goals    simp [h6] at a   <;> omega