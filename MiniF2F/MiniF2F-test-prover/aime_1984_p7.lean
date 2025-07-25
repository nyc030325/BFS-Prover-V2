import Mathlib
open BigOperators Real Nat Topology

theorem aime_1984_p7
  (f : ℤ → ℤ)
  (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
  (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) :
  f 84 = 997 := by

  inhabit ℤ
  set_option maxRecDepth 1997 in
    have hᵢ := h₁ 84 (by norm_num)
    norm_cast at hᵢ <;>
  simp [h₀, h₁] at * <;>
  linarith