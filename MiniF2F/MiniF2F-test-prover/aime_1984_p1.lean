import Mathlib
open BigOperators Real Nat Topology

theorem aime_1984_p1
  (u : ℕ → ℚ)
  (h₀ : ∀ n, u (n + 1) = u n + 1)
  (h₁ : ∑ k in Finset.range 98, u k.succ = 137) :
  ∑ k in Finset.range 49, u (2 * k.succ) = 93 := by

  have ab₀ : ∀ n, u n = u 0 + n := by
    intro n
    induction' n with r hr
    simp
    simp [h₀]
    linarith [hr]
  set a := u 0
  simp only [Finset.sum_range_succ, ab₀] at h₁ ⊢
  norm_num [mul_add] at h₁ ⊢ <;>
    linarith